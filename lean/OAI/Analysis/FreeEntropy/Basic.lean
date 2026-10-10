import OAI.Analysis.FreeEntropy.Model

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter

namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] theorem trace_zero {M : VonNeumannAlgebra H} (τ : TracialVector M) :
    trace τ (0 : H →L[ℂ] H) = 0 := by simp [trace]

 theorem trace_add {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A B : H →L[ℂ] H) : trace τ (A + B) = trace τ A + trace τ B := by
  simp [trace]

 theorem trace_smul {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (z : ℂ) (A : H →L[ℂ] H) : trace τ (z • A) = z * trace τ A := by
  simp [trace]

 theorem trace_sum {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {α : Type u1} (s : Finset α) (A : α → H →L[ℂ] H) :
    trace τ (∑ a ∈ s, A a) = ∑ a ∈ s, trace τ (A a) := by
  simp [trace]

theorem ConjugateSystem.unique {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ η : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (hη : ConjugateSystem τ X η) : ξ = η := by
  funext i
  have hmem : ξ i - η i ∈ polynomialL2 τ X :=
    (polynomialL2 τ X).sub_mem (hξ i).1 (hη i).1
  have hker : polynomialL2 τ X ≤ (innerSL ℂ (ξ i - η i)).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      change inner ℂ (ξ i - η i) (wordEval X w τ.vacuum) = 0
      rw [inner_sub_left, (hξ i).2 w, (hη i).2 w, sub_self]
    · exact (innerSL ℂ (ξ i - η i)).isClosed_ker
  have hd : inner ℂ (ξ i - η i) (ξ i - η i) = 0 := hker hmem
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hd)

theorem freeFisher_eq_of_conjugate {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) :
    freeFisher τ X = ENNReal.ofReal (∑ i, ‖ξ i‖ ^ 2) := by
  apply le_antisymm
  · exact iInf_le_of_le ξ (iInf_le_of_le hξ le_rfl)
  · refine le_iInf fun η => le_iInf fun hη => ?_
    rw [hξ.unique τ hη]

@[simp] theorem trace_one {M : VonNeumannAlgebra H} (τ : TracialVector M) :
    trace τ (1 : H →L[ℂ] H) = 1 := by
  simp [trace, inner_self_eq_norm_sq_to_K, τ.norm_vacuum]

@[simp] theorem wordMoment_nil {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) : wordMoment τ X [] = 1 := by
  simp [wordMoment, wordEval]

 theorem wordVector_mem_polynomialL2 {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (w : List (Fin n)) :
    wordEval X w τ.vacuum ∈ polynomialL2 τ X :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩)

instance polynomialL2_complete {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) : CompleteSpace (polynomialL2 τ X) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def projectedConjugate {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H) (i : Fin n) : H :=
  (polynomialL2 τ X).starProjection (η i)

 theorem projectedConjugate_system {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H)
    (hη : ∀ i w, inner ℂ (η i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w) :
    ConjugateSystem τ X (projectedConjugate τ X η) := by
  intro i
  refine ⟨(polynomialL2 τ X).starProjection_apply_mem _, fun w => ?_⟩
  have h := (polynomialL2 τ X).starProjection_inner_eq_zero (η i)
    (wordEval X w τ.vacuum) (wordVector_mem_polynomialL2 τ X w)
  rw [inner_sub_left, hη i w] at h
  exact (sub_eq_zero.mp h).symm

theorem freeFisher_le_testVectors {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H)
    (hη : ∀ i w, inner ℂ (η i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w) :
    freeFisher τ X ≤ ENNReal.ofReal (∑ i, ‖η i‖ ^ 2) := by
  rw [freeFisher_eq_of_conjugate τ (projectedConjugate_system τ X η hη)]
  apply ENNReal.ofReal_le_ofReal
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) ((polynomialL2 τ X).norm_starProjection_apply_le _) _

 theorem conjugate_coordinate_pairing {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) : inner ℂ (ξ i) (X i τ.vacuum) = 1 := by
  have h := (hξ i).2 [i]
  simpa [wordEval, derivativeMoment, wordMoment, trace_one] using h

theorem conjugate_norm_sq_lower {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) :
    1 / ‖X i τ.vacuum‖ ^ 2 ≤ ‖ξ i‖ ^ 2 := by
  have h : 1 ≤ ‖ξ i‖ * ‖X i τ.vacuum‖ := by
    simpa only [conjugate_coordinate_pairing τ hξ i, norm_one] using
      norm_inner_le_norm (𝕜 := ℂ) (ξ i) (X i τ.vacuum)
  have hp : 0 < ‖X i τ.vacuum‖ := by
    have hn := norm_nonneg (X i τ.vacuum)
    by_contra hh
    have hz : ‖X i τ.vacuum‖ = 0 := le_antisymm (not_lt.mp hh) hn
    rw [hz, mul_zero] at h
    linarith
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  nlinarith [sq_nonneg (‖ξ i‖ * ‖X i τ.vacuum‖ - 1)]

 theorem freeFisher_lower_covariance {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) :
    ENNReal.ofReal (∑ i, 1 / ‖X i τ.vacuum‖ ^ 2) ≤ freeFisher τ X := by
  refine le_iInf fun ξ => le_iInf fun hξ => ?_
  apply ENNReal.ofReal_le_ofReal
  exact Finset.sum_le_sum fun i _ => conjugate_norm_sq_lower τ hξ i

def vacuumRankOne {M : VonNeumannAlgebra H} (τ : TracialVector M) : H →L[ℂ] H :=
  InnerProductSpace.rankOne ℂ τ.vacuum τ.vacuum

def commutatorKernel {n : ℕ} (P : H →L[ℂ] H) (X : Fin n → H →L[ℂ] H)
    (i : Fin n) (w : List (Fin n)) : H →L[ℂ] H :=
  ∑ r : Fin w.length, if w[r.val] = i then
    wordEval X (w.take r.val) * P * wordEval X (w.drop (r.val + 1)) else 0

omit [CompleteSpace H] in
@[simp] theorem commutatorKernel_nil {n : ℕ} (P : H →L[ℂ] H)
    (X : Fin n → H →L[ℂ] H) (i : Fin n) : commutatorKernel P X i [] = 0 := by
  simp [commutatorKernel]

omit [CompleteSpace H] in
 theorem commutatorKernel_cons {n : ℕ} (P : H →L[ℂ] H)
    (X : Fin n → H →L[ℂ] H) (i j : Fin n) (w : List (Fin n)) :
    commutatorKernel P X i (j :: w) =
      (if j = i then P * wordEval X w else 0) + X j * commutatorKernel P X i w := by
  simp only [commutatorKernel, List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_zero, List.take_succ_cons, List.drop_succ_cons, Nat.zero_add,
    wordEval, List.map_nil, List.prod_nil, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [List.map_cons, List.prod_cons, mul_assoc]

omit [CompleteSpace H] in
 theorem commutator_word {n : ℕ} (P a : H →L[ℂ] H) (X : Fin n → H →L[ℂ] H)
    (i : Fin n) (c : ℂ)
    (h : ∀ j, a * X j = X j * a + if j = i then c • P else 0)
    (w : List (Fin n)) :
    a * wordEval X w = wordEval X w * a + c • commutatorKernel P X i w := by
  induction w with
  | nil => simp [wordEval]
  | cons j w ih =>
    have hw : wordEval X (j :: w) = X j * wordEval X w := by simp [wordEval]
    rw [hw, commutatorKernel_cons, ← mul_assoc, h, add_mul, mul_assoc, ih]
    by_cases hji : j = i <;>
      simp [hji, mul_add, mul_assoc, smul_add, _root_.add_assoc, _root_.add_comm,
        _root_.add_left_comm]

 theorem trace_vacuumRankOne_product {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A B : H →L[ℂ] H) : trace τ (A * vacuumRankOne τ * B) = trace τ A * trace τ B := by
  simp only [trace, vacuumRankOne, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
    map_smul, inner_smul_right]
  exact mul_comm _ _

 theorem trace_commutatorKernel {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : List (Fin n)) :
    trace τ (commutatorKernel (vacuumRankOne τ) X i w) = derivativeMoment τ X i w := by
  rw [commutatorKernel, trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [trace_vacuumRankOne_product, wordMoment]

theorem commutator_integration_by_parts {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (a : H →L[ℂ] H) (i : Fin n) (c : ℂ)
    (h : ∀ j, a * X j = X j * a + if j = i then c • vacuumRankOne τ else 0)
    (hz : a τ.vacuum = 0) (w : List (Fin n)) :
    inner ℂ (star a τ.vacuum) (wordEval X w τ.vacuum) = c * derivativeMoment τ X i w := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  change trace τ (a * wordEval X w) = _
  rw [commutator_word _ _ _ _ _ h, trace_add, trace_smul, trace_commutatorKernel]
  have hzero : trace τ (wordEval X w * a) = 0 := by
    simp [trace, mul_apply_eq_comp, hz]
  rw [hzero, zero_add]

theorem FreeSubalgebras.mono {κ : Type} {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {A B : κ → Subalgebra ℂ (H →L[ℂ] H)} (hA : FreeSubalgebras τ A)
    (hBA : ∀ i, B i ≤ A i) : FreeSubalgebras τ B := by
  intro k hk j a ha hc hadj
  exact hA k hk j a (fun r => hBA (j r) (ha r)) hc hadj

namespace Fock

open scoped lp
variable {ι : Type} [DecidableEq ι]

abbrev Space (ι : Type) := lp (fun _ : List ι => ℂ) 2

instance space_nontrivial : Nontrivial (Space ι) := by
  refine ⟨⟨lp.single 2 ([] : List ι) (1 : ℂ), 0, ?_⟩⟩
  intro h
  have he := congrArg (fun f : Space ι => f []) h
  simp at he

def basisVector (w : List ι) : Space ι := lp.single 2 w 1

def coordinateIsometry (w : List ι) : ℂ →ₗᵢ[ℂ] Space ι where
  toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : List ι => ℂ) 2 w
  norm_map' z := lp.norm_single (E := fun _ : List ι => ℂ) (p := 2) (by norm_num) w z

@[simp] theorem coordinateIsometry_apply (w : List ι) (z : ℂ) :
    coordinateIsometry w z = lp.single 2 w z := rfl

theorem orthogonal_coordinates (f : List ι → List ι) (hf : Function.Injective f) :
    OrthogonalFamily ℂ (fun _ : List ι => ℂ) (fun w => coordinateIsometry (f w)) := by
  intro w v hwv a b
  simp only [coordinateIsometry_apply, lp.inner_single_left]
  rw [lp.single_apply_ne (E := fun _ : List ι => ℂ) 2 (f v) b (fun h => hwv (hf h))]
  simp

def injectionIsometry (f : List ι → List ι) (hf : Function.Injective f) :
    Space ι →ₗᵢ[ℂ] Space ι :=
  (orthogonal_coordinates f hf).linearIsometry

@[simp] theorem injectionIsometry_single (f : List ι → List ι)
    (hf : Function.Injective f) (w : List ι) (z : ℂ) :
    injectionIsometry f hf (lp.single 2 w z) = lp.single 2 (f w) z := by
  exact (orthogonal_coordinates f hf).linearIsometry_apply_single z

def creation (i : ι) : Space ι →L[ℂ] Space ι :=
  (injectionIsometry (List.cons i) (List.cons_injective (a := i))).toContinuousLinearMap

def rightCreation (i : ι) : Space ι →L[ℂ] Space ι :=
  (injectionIsometry (fun w => w ++ [i]) (List.append_left_injective [i])).toContinuousLinearMap

@[simp] theorem creation_single (i : ι) (w : List ι) (z : ℂ) :
    creation i (lp.single 2 w z) = lp.single 2 (i :: w) z := by
  exact injectionIsometry_single (List.cons i) List.cons_injective w z

@[simp] theorem rightCreation_single (i : ι) (w : List ι) (z : ℂ) :
    rightCreation i (lp.single 2 w z) = lp.single 2 (w ++ [i]) z := by
  exact injectionIsometry_single (fun w => w ++ [i]) (List.append_left_injective [i]) w z

def semicircular (i : ι) : Space ι →L[ℂ] Space ι := creation i + star (creation i)

def rightSemicircular (i : ι) : Space ι →L[ℂ] Space ι :=
  rightCreation i + star (rightCreation i)

theorem semicircular_selfAdjoint (i : ι) : IsSelfAdjoint (semicircular i) :=
  IsSelfAdjoint.add_star_self (creation i)

theorem rightSemicircular_selfAdjoint (i : ι) : IsSelfAdjoint (rightSemicircular i) :=
  IsSelfAdjoint.add_star_self (rightCreation i)

theorem semicircular_norm_le (i : ι) : ‖semicircular i‖ ≤ 2 := by
  calc
    ‖semicircular i‖ ≤ ‖creation i‖ + ‖star (creation i)‖ := norm_add_le _ _
    _ = 2 := by norm_num [creation, ContinuousLinearMap.star_eq_adjoint, LinearIsometry.norm_toContinuousLinearMap]

@[simp] theorem adjoint_creation_apply (i : ι) (x : Space ι) (w : List ι) :
    (star (creation i) x) w = x (i :: w) := by
  have h := ContinuousLinearMap.adjoint_inner_right (creation i) (lp.single 2 w (1 : ℂ)) x
  simpa [ContinuousLinearMap.star_eq_adjoint, lp.inner_single_left] using h

@[simp] theorem adjoint_rightCreation_apply (i : ι) (x : Space ι) (w : List ι) :
    (star (rightCreation i) x) w = x (w ++ [i]) := by
  have h := ContinuousLinearMap.adjoint_inner_right (rightCreation i) (lp.single 2 w (1 : ℂ)) x
  simpa [ContinuousLinearMap.star_eq_adjoint, lp.inner_single_left] using h

@[simp] theorem annihilation_single_nil (i : ι) (z : ℂ) :
    star (creation i) (lp.single 2 ([] : List ι) z) = 0 := by
  apply lp.ext
  funext w
  simp [lp.single_apply]

@[simp] theorem annihilation_single_cons (i j : ι) (w : List ι) (z : ℂ) :
    star (creation i) (lp.single 2 (j :: w) z) =
      if i = j then lp.single 2 w z else 0 := by
  apply lp.ext
  funext v
  by_cases h : i = j
  · subst j
    simp [lp.single_apply, Pi.single_apply]
  · simp [lp.single_apply, h]

@[simp] theorem rightAnnihilation_single_nil (i : ι) (z : ℂ) :
    star (rightCreation i) (lp.single 2 ([] : List ι) z) = 0 := by
  apply lp.ext
  funext w
  simp [lp.single_apply]

@[simp] theorem rightAnnihilation_single_append (i j : ι) (w : List ι) (z : ℂ) :
    star (rightCreation i) (lp.single 2 (w ++ [j]) z) =
      if i = j then lp.single 2 w z else 0 := by
  apply lp.ext
  funext v
  by_cases h : i = j
  · subst j
    simp [lp.single_apply, Pi.single_apply]
  · simp [lp.single_apply, h]

@[simp] theorem semicircular_single_nil (i : ι) (z : ℂ) :
    semicircular i (lp.single 2 ([] : List ι) z) = lp.single 2 [i] z := by
  simp [semicircular]

@[simp] theorem semicircular_single_cons (i j : ι) (w : List ι) (z : ℂ) :
    semicircular i (lp.single 2 (j :: w) z) =
      lp.single 2 (i :: j :: w) z + if i = j then lp.single 2 w z else 0 := by
  simp [semicircular]

@[simp] theorem rightSemicircular_single_nil (i : ι) (z : ℂ) :
    rightSemicircular i (lp.single 2 ([] : List ι) z) = lp.single 2 [i] z := by
  simp [rightSemicircular]

@[simp] theorem rightSemicircular_single_append (i j : ι) (w : List ι) (z : ℂ) :
    rightSemicircular i (lp.single 2 (w ++ [j]) z) =
      lp.single 2 (w ++ [j, i]) z + if i = j then lp.single 2 w z else 0 := by
  simp [rightSemicircular]

theorem semicircular_commutes_right (i j : ι) :
    Commute (semicircular i) (rightSemicircular j) := by
  show semicircular i * rightSemicircular j = rightSemicircular j * semicircular i
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change semicircular i (rightSemicircular j (lp.single 2 w z)) =
    rightSemicircular j (semicircular i (lp.single 2 w z))
  cases w with
  | nil =>
    simp only [rightSemicircular_single_nil, semicircular_single_nil,
      semicircular_single_cons]
    rw [show [i] = [] ++ [i] from rfl, rightSemicircular_single_append]
    by_cases h : i = j <;> simp [h, eq_comm]
  | cons k v =>
    induction v using List.reverseRecOn with
    | nil =>
      rw [show [k] = [] ++ [k] from rfl, rightSemicircular_single_append]
      simp only [List.nil_append, map_add, semicircular_single_cons]
      rw [show [i, k] = [i] ++ [k] from rfl, rightSemicircular_single_append]
      by_cases hik : i = k <;> by_cases hjk : j = k <;>
        simp [hik, hjk, rightSemicircular_single_nil]
    | append_singleton v l _ =>
      rw [show k :: (v ++ [l]) = (k :: v) ++ [l] from rfl,
        rightSemicircular_single_append]
      simp only [map_add, List.cons_append, semicircular_single_cons]
      rw [show i :: k :: (v ++ [l]) = (i :: k :: v) ++ [l] from rfl,
        rightSemicircular_single_append]
      by_cases hik : i = k <;> by_cases hjl : j = l <;>
        simp [hik, hjl, rightSemicircular_single_append, add_assoc, add_comm, add_left_comm]

def rightWick : List ι → Space ι →L[ℂ] Space ι
  | [] => 1
  | [i] => rightSemicircular i
  | i :: j :: w => rightSemicircular i * rightWick (j :: w) -
      if i = j then rightWick w else 0

 theorem commute_rightWick (A : Space ι →L[ℂ] Space ι)
    (h : ∀ i, Commute A (rightSemicircular i)) (w : List ι) :
    Commute A (rightWick w) := by
  induction w using rightWick.induct with
  | case1 => exact Commute.one_right A
  | case2 i => exact h i
  | case3 i j w ih₁ ih₂ =>
    dsimp only [rightWick]
    apply ((h i).mul_right ih₁).sub_right
    split_ifs
    · exact ih₂
    · exact Commute.zero_right A

@[simp] theorem rightWick_vacuum (w : List ι) :
    rightWick w (basisVector []) = basisVector w.reverse := by
  induction w using rightWick.induct with
  | case1 => simp [rightWick]
  | case2 i => simp [rightWick, basisVector]
  | case3 i j w ih₁ ih₂ =>
    simp only [rightWick, sub_apply, mul_apply_eq_comp, ih₁]
    by_cases h : i = j <;>
      simp only [h, ↓reduceIte, ih₂] <;>
      simp [basisVector, List.reverse_cons, h, rightSemicircular_single_append]

@[simp] theorem adjoint_rightWick_vacuum (w : List ι) :
    star (rightWick w) (basisVector []) = basisVector w := by
  induction w using rightWick.induct with
  | case1 => simp [rightWick]
  | case2 i =>
    rw [rightWick, (rightSemicircular_selfAdjoint i).star_eq]
    simp [basisVector]
  | case3 i j w ih₁ ih₂ =>
    have hc : Commute (star (rightWick (j :: w))) (semicircular i) := by
      have h := commute_rightWick (semicircular i) (semicircular_commutes_right i) (j :: w)
      have hs := congrArg star h.eq
      change _ * _ = _ * _
      simpa only [star_mul, (semicircular_selfAdjoint i).star_eq] using hs
    have hv : rightSemicircular i (basisVector ([] : List ι)) =
        semicircular i (basisVector []) := by simp [basisVector]
    rw [rightWick, star_sub (rightSemicircular i * rightWick (j :: w)) _, star_mul,
      (rightSemicircular_selfAdjoint i).star_eq,
      sub_apply, mul_apply_eq_comp]
    rw [hv, ← mul_apply_eq_comp, hc.eq, mul_apply_eq_comp, ih₁]
    by_cases h : i = j <;>
      simp only [h, ↓reduceIte, star_zero, ih₂] <;>
      simp [h, basisVector]

def algebra (ι : Type) [DecidableEq ι] : VonNeumannAlgebra (Space ι) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (Set.range (rightSemicircular (ι := ι)))
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer _

 theorem mem_algebra_iff (A : Space ι →L[ℂ] Space ι) :
    A ∈ algebra ι ↔ ∀ i, Commute A (rightSemicircular i) := by
  change A ∈ StarSubalgebra.centralizer ℂ (Set.range rightSemicircular) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  simp only [Set.forall_mem_range, (rightSemicircular_selfAdjoint _).star_eq, and_self]
  exact forall_congr' fun i => eq_comm

 theorem semicircular_mem (i : ι) : semicircular i ∈ algebra ι :=
  (mem_algebra_iff _).mpr (semicircular_commutes_right i)

theorem vacuum_separating (A : Space ι →L[ℂ] Space ι) (hA : A ∈ algebra ι)
    (h0 : A (basisVector []) = 0) : A = 0 := by
  have hsingle (w : List ι) : A (basisVector w) = 0 := by
    rw [← List.reverse_reverse w, ← rightWick_vacuum]
    rw [← mul_apply_eq_comp,
      (commute_rightWick A ((mem_algebra_iff A).mp hA) w.reverse).eq,
      mul_apply_eq_comp, h0, map_zero]
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change A (lp.single 2 w z) = 0
  have hz : lp.single 2 w z = z • basisVector w := by
    simp [basisVector, ← lp.single_smul]
  rw [hz, map_smul, hsingle, smul_zero]

theorem adjoint_vacuum_coefficient (A : Space ι →L[ℂ] Space ι)
    (hA : A ∈ algebra ι) (w : List ι) :
    (star A (basisVector [])) w = star ((A (basisVector [])) w.reverse) := by
  have hw : A (basisVector w) = rightWick w.reverse (A (basisVector [])) := by
    rw [← mul_apply_eq_comp,
      ← (commute_rightWick A ((mem_algebra_iff A).mp hA) w.reverse).eq,
      mul_apply_eq_comp, rightWick_vacuum, List.reverse_reverse]
  calc
    (star A (basisVector [])) w = inner ℂ (basisVector w) (star A (basisVector [])) := by
      simp [basisVector, lp.inner_single_left]
    _ = inner ℂ (A (basisVector w)) (basisVector []) :=
      ContinuousLinearMap.adjoint_inner_right A _ _
    _ = inner ℂ (rightWick w.reverse (A (basisVector []))) (basisVector []) := by rw [hw]
    _ = inner ℂ (A (basisVector [])) (star (rightWick w.reverse) (basisVector [])) :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = star ((A (basisVector [])) w.reverse) := by
      rw [adjoint_rightWick_vacuum]
      simp [basisVector, lp.inner_single_right]

 theorem vacuum_product_formula (A B : Space ι →L[ℂ] Space ι)
    (hA : A ∈ algebra ι) :
    inner ℂ (basisVector []) ((A * B) (basisVector [])) =
      ∑' w : List ι, (B (basisVector [])) w * (A (basisVector [])) w.reverse := by
  rw [mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left A,
    ← ContinuousLinearMap.star_eq_adjoint, lp.inner_eq_tsum]
  apply tsum_congr
  intro w
  rw [RCLike.inner_apply, adjoint_vacuum_coefficient A hA w]
  simp

theorem vacuum_tracial (A : Space ι →L[ℂ] Space ι) (hA : A ∈ algebra ι)
    (B : Space ι →L[ℂ] Space ι) (hB : B ∈ algebra ι) :
    inner ℂ (basisVector []) ((A * B) (basisVector [])) =
      inner ℂ (basisVector []) ((B * A) (basisVector [])) := by
  rw [vacuum_product_formula A B hA, vacuum_product_formula B A hB]
  let e : List ι ≃ List ι := ⟨List.reverse, List.reverse, List.reverse_reverse, List.reverse_reverse⟩
  calc
    (∑' w : List ι, (B (basisVector [])) w * (A (basisVector [])) w.reverse) =
        ∑' w : List ι, (B (basisVector [])) w.reverse * (A (basisVector [])) w := by
      simpa [e] using (e.tsum_eq (fun w : List ι =>
        (B (basisVector [])) w * (A (basisVector [])) w.reverse)).symm
    _ = _ := tsum_congr fun _ => mul_comm _ _

def tracialVector (ι : Type) [DecidableEq ι] : TracialVector (algebra ι) where
  vacuum := basisVector []
  norm_vacuum := by
    simp [basisVector, lp.norm_single (E := fun _ : List ι => ℂ) (p := 2)]
  tracial := vacuum_tracial
  separating := vacuum_separating

def vacuumProjection : Space ι →L[ℂ] Space ι :=
  InnerProductSpace.rankOne ℂ (basisVector []) (basisVector [])

@[simp] theorem vacuumProjection_single (w : List ι) (z : ℂ) :
    vacuumProjection (lp.single 2 w z) = if w = [] then lp.single 2 [] z else 0 := by
  by_cases h : w = []
  · subst w
    simp [vacuumProjection, basisVector, lp.inner_single_left, ← lp.single_smul]
  · simp [vacuumProjection, basisVector, lp.inner_single_left, lp.single_apply, h]

 theorem creation_commutes_rightCreation (i j : ι) :
    Commute (creation i) (rightCreation j) := by
  show creation i * rightCreation j = rightCreation j * creation i
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change creation i (rightCreation j (lp.single 2 w z)) =
    rightCreation j (creation i (lp.single 2 w z))
  simp

 theorem rightAnnihilation_creation (i j : ι) :
    star (rightCreation i) * creation j = creation j * star (rightCreation i) +
      if i = j then vacuumProjection else 0 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (rightCreation i) (creation j (lp.single 2 w z)) =
    creation j (star (rightCreation i) (lp.single 2 w z)) +
      (if i = j then vacuumProjection else 0) (lp.single 2 w z)
  induction w using List.reverseRecOn with
  | nil =>
    rw [creation_single, show [j] = [] ++ [j] from rfl, rightAnnihilation_single_append]
    by_cases h : i = j <;> simp [h]
  | append_singleton w k _ =>
    rw [creation_single, show j :: (w ++ [k]) = (j :: w) ++ [k] from rfl,
      rightAnnihilation_single_append]
    have hp : (if i = j then vacuumProjection else 0) (lp.single 2 (w ++ [k]) z) = 0 := by
      split_ifs <;> simp
    rw [hp, rightAnnihilation_single_append]
    by_cases h : i = k <;> simp [h]

theorem rightAnnihilation_semicircular (i j : ι) :
    star (rightCreation i) * semicircular j = semicircular j * star (rightCreation i) +
      if i = j then vacuumProjection else 0 := by
  have h : star (rightCreation i) * star (creation j) =
      star (creation j) * star (rightCreation i) := by
    simpa only [star_mul] using congrArg star (creation_commutes_rightCreation j i).eq
  rw [semicircular, mul_add, add_mul, rightAnnihilation_creation, h]
  abel

def derivativeKernel {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    Space (Fin n) →L[ℂ] Space (Fin n) :=
  ∑ r : Fin w.length, if w[r.val] = i then
    wordEval semicircular (w.take r.val) * vacuumProjection *
      wordEval semicircular (w.drop (r.val + 1)) else 0

@[simp] theorem derivativeKernel_nil {n : ℕ} (i : Fin n) :
    derivativeKernel i [] = 0 := by simp [derivativeKernel]

 theorem derivativeKernel_cons {n : ℕ} (i j : Fin n) (w : List (Fin n)) :
    derivativeKernel i (j :: w) =
      (if j = i then vacuumProjection * wordEval semicircular w else 0) +
        semicircular j * derivativeKernel i w := by
  simp only [derivativeKernel, List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_zero, List.take_succ_cons, List.drop_succ_cons, Nat.zero_add,
    wordEval, List.map_nil, List.prod_nil, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [List.map_cons, List.prod_cons, mul_assoc]

 theorem rightAnnihilation_word {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    star (rightCreation i) * wordEval semicircular w =
      wordEval semicircular w * star (rightCreation i) + derivativeKernel i w := by
  induction w with
  | nil => simp [wordEval]
  | cons j w ih =>
    have hw : wordEval semicircular (j :: w) = semicircular j * wordEval semicircular w := by
      simp [wordEval]
    rw [hw, derivativeKernel_cons, ← mul_assoc, rightAnnihilation_semicircular,
      add_mul, mul_assoc, ih, mul_add]
    by_cases h : i = j <;> simp [h, eq_comm, mul_assoc, add_assoc, add_comm, add_left_comm]

 theorem trace_projection_product (A B : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) (A * vacuumProjection * B) =
      trace (tracialVector ι) A * trace (tracialVector ι) B := by
  simp only [trace, tracialVector, vacuumProjection, mul_apply_eq_comp,
    InnerProductSpace.rankOne_apply, map_smul, inner_smul_right]
  exact mul_comm _ _

 theorem trace_derivativeKernel {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    trace (tracialVector (Fin n)) (derivativeKernel i w) =
      derivativeMoment (tracialVector (Fin n)) semicircular i w := by
  rw [derivativeKernel, trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [trace_projection_product, wordMoment]

 theorem trace_semicircular_left (i : ι) (A : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) (semicircular i * A) =
      trace (tracialVector ι) (star (rightCreation i) * A) := by
  simp only [trace, tracialVector, mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_left (semicircular i),
    ← ContinuousLinearMap.adjoint_inner_left (star (rightCreation i))]
  simp only [← ContinuousLinearMap.star_eq_adjoint, star_star,
    (semicircular_selfAdjoint i).star_eq, basisVector,
    semicircular_single_nil, rightCreation_single, List.nil_append]

theorem semicircular_integration_by_parts {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    trace (tracialVector (Fin n)) (semicircular i * wordEval semicircular w) =
      derivativeMoment (tracialVector (Fin n)) semicircular i w := by
  rw [trace_semicircular_left, rightAnnihilation_word, trace_add, trace_derivativeKernel]
  suffices trace (tracialVector (Fin n))
      (wordEval semicircular w * star (rightCreation i)) = 0 by rw [this, zero_add]
  simp [trace, tracialVector, basisVector, mul_apply_eq_comp]

theorem semicircular_conjugateSystem (n : ℕ) :
    ConjugateSystem (tracialVector (Fin n)) semicircular
      (fun i => semicircular i (basisVector [])) := by
  intro i
  constructor
  · apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    use [i]
    simp [wordEval, tracialVector]
  · intro w
    rw [← semicircular_integration_by_parts]
    change inner ℂ (semicircular i (basisVector [])) (wordEval semicircular w (basisVector [])) =
      inner ℂ (basisVector []) (semicircular i (wordEval semicircular w (basisVector [])))
    conv_lhs => rw [← (semicircular_selfAdjoint i).star_eq]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

theorem semicircular_freeFisher (n : ℕ) :
    freeFisher (tracialVector (Fin n)) semicircular = (n : ℝ≥0∞) := by
  rw [freeFisher_eq_of_conjugate _ (semicircular_conjugateSystem n)]
  simp [basisVector, lp.norm_single (E := fun _ : List (Fin n) => ℂ) (p := 2)]

theorem semicircular_moment_succ {n : ℕ} (i : Fin n) (k : ℕ) :
    trace (tracialVector (Fin n)) (semicircular i ^ (k + 1)) =
      ∑ r ∈ Finset.range k, trace (tracialVector (Fin n)) (semicircular i ^ r) *
        trace (tracialVector (Fin n)) (semicircular i ^ (k - (r + 1))) := by
  have hw (j : ℕ) : wordEval semicircular (List.replicate j i) = semicircular i ^ j := by
    simp [wordEval]
  rw [pow_succ', ← hw k, semicircular_integration_by_parts]
  simp only [derivativeMoment, List.getElem_replicate,
    ite_true, wordMoment, List.take_replicate, List.drop_replicate]
  simp only [hw]
  rw [Fin.sum_univ_eq_sum_range (fun r =>
    trace (tracialVector (Fin n)) (semicircular i ^ min r k) *
      trace (tracialVector (Fin n)) (semicircular i ^ (k - (r + 1))))
    (List.replicate k i).length, List.length_replicate]
  apply Finset.sum_congr rfl
  intro r hr
  rw [min_eq_left (Nat.le_of_lt (Finset.mem_range.mp hr))]

private theorem sum_range_double {α : Type u2} [AddCommMonoid α] (f : ℕ → α) (k : ℕ) :
    ∑ r ∈ Finset.range (2 * k), f r =
      ∑ r ∈ Finset.range k, (f (2 * r) + f (2 * r + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, show 2 * k + 2 = (2 * k + 1) + 1 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

theorem semicircular_moments {n : ℕ} (i : Fin n) (k : ℕ) :
    trace (tracialVector (Fin n)) (semicircular i ^ k) =
      if Even k then (catalan (k / 2) : ℂ) else 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp [trace, tracialVector, basisVector]
    · rw [semicircular_moment_succ]
      rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
      · rw [ite_eq_right (by rw [Nat.even_iff]; omega : ¬Even (2 * m + 1))]
        apply Finset.sum_eq_zero
        intro r hr
        have hr' := Finset.mem_range.mp hr
        rw [ih r (by omega), ih (2 * m - (r + 1)) (by omega)]
        rcases Nat.mod_two_eq_zero_or_one r with he | ho
        · have : ¬ Even (2 * m - (r + 1)) := by rw [Nat.even_iff]; omega
          simp [this]
        · have : ¬ Even r := by rw [Nat.even_iff]; omega
          simp [this]
      · have he : Even (2 * m + 1 + 1) := by rw [Nat.even_iff]; omega
        rw [ite_eq_left he, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
          Finset.sum_range_succ, sum_range_double]
        have hs : ∀ r < m,
            trace (tracialVector (Fin n)) (semicircular i ^ (2 * r)) *
                trace (tracialVector (Fin n)) (semicircular i ^ (2 * m + 1 - (2 * r + 1))) +
              trace (tracialVector (Fin n)) (semicircular i ^ (2 * r + 1)) *
                trace (tracialVector (Fin n)) (semicircular i ^ (2 * m + 1 - (2 * r + 1 + 1))) =
            (catalan r : ℂ) * (catalan (m - r) : ℂ) := by
          intro r hr
          rw [ih (2 * r) (by omega), ih (2 * m + 1 - (2 * r + 1)) (by omega),
            ih (2 * r + 1) (by omega)]
          have h₁ : Even (2 * r) := by rw [Nat.even_iff]; omega
          have h₂ : Even (2 * m + 1 - (2 * r + 1)) := by rw [Nat.even_iff]; omega
          have h₃ : ¬Even (2 * r + 1) := by rw [Nat.even_iff]; omega
          simp only [h₁, h₂, h₃, ite_true, ite_false, zero_mul, add_zero]
          rw [show 2 * r / 2 = r by omega,
            show (2 * m + 1 - (2 * r + 1)) / 2 = m - r by omega]
        rw [Finset.sum_congr rfl (fun r hr => hs r (Finset.mem_range.mp hr))]
        rw [ih (2 * m) (by omega), ih (2 * m + 1 - (2 * m + 1)) (by omega)]
        have h₁ : Even (2 * m) := by rw [Nat.even_iff]; omega
        simp only [Nat.sub_self, h₁, ite_true, show Even (0 : ℕ) from ⟨0, rfl⟩, Nat.zero_div,
          catalan_zero, Nat.cast_one, mul_one]
        rw [show 2 * m / 2 = m by omega, catalan_succ,
          Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, catalan_zero,
          mul_one, Nat.cast_mul]

def wordSpace (J : Set ι) : Submodule ℂ (Space ι) :=
  Submodule.span ℂ {x | ∃ w : List ι, (∀ i ∈ w, i ∈ J) ∧ x = basisVector w}

def startsIn (J : Set ι) : Submodule ℂ (Space ι) :=
  Submodule.span ℂ {x | ∃ i ∈ J, ∃ w : List ι, x = basisVector (i :: w)}

def suffixEmbedding (w : List ι) : Space ι →L[ℂ] Space ι :=
  (injectionIsometry (fun v => v ++ w) (List.append_left_injective w)).toContinuousLinearMap

@[simp] theorem suffixEmbedding_basis (w v : List ι) :
    suffixEmbedding w (basisVector v) = basisVector (v ++ w) :=
  injectionIsometry_single _ (List.append_left_injective w) v 1

 theorem basis_mem_wordSpace {J : Set ι} {w : List ι} (hw : ∀ i ∈ w, i ∈ J) :
    basisVector w ∈ wordSpace J := Submodule.subset_span ⟨w, hw, rfl⟩

 theorem vacuum_mem_wordSpace (J : Set ι) : basisVector [] ∈ wordSpace J :=
  basis_mem_wordSpace (by simp)

 theorem semicircular_preserves_wordSpace {J : Set ι} {i : ι} (hi : i ∈ J)
    {x : Space ι} (hx : x ∈ wordSpace J) : semicircular i x ∈ wordSpace J := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    cases w with
    | nil =>
      simpa [basisVector] using
        (basis_mem_wordSpace (show ∀ j ∈ [i], j ∈ J by simpa using hi))
    | cons j w =>
      change semicircular i (lp.single 2 (j :: w) 1) ∈ wordSpace J
      rw [semicircular_single_cons]
      apply Submodule.add_mem
      · exact basis_mem_wordSpace (by simpa using And.intro hi hw)
      · split_ifs
        · exact basis_mem_wordSpace (fun k hk => hw k (List.mem_cons_of_mem _ hk))
        · exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa using (wordSpace J).add_mem hx hy
  | smul z x _ hx => simpa using (wordSpace J).smul_mem z hx

 theorem semicircular_suffix {J : Set ι} {i : ι} (hi : i ∈ J)
    (w : List ι) (hw : ∀ j ∈ w.head?, j ∉ J) {x : Space ι} (hx : x ∈ wordSpace J) :
    semicircular i (suffixEmbedding w x) = suffixEmbedding w (semicircular i x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    cases v with
    | nil =>
      cases w with
      | nil => simp [basisVector, suffixEmbedding, injectionIsometry_single]
      | cons j w =>
        have hij : i ≠ j := by intro hij; subst i; exact hw j (by simp) hi
        simp [basisVector, suffixEmbedding, injectionIsometry_single, hij]
    | cons j v =>
      change semicircular i (suffixEmbedding w (lp.single 2 (j :: v) 1)) = _
      rw [show suffixEmbedding w (lp.single 2 (j :: v) 1) =
        lp.single 2 (j :: (v ++ w)) 1 from suffixEmbedding_basis w (j :: v)]
      simp only [basisVector, semicircular_single_cons, map_add]
      split_ifs <;> simp [suffixEmbedding, injectionIsometry_single]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul z x _ hx => simp [hx]

theorem adjoin_suffix {J : Set ι} {A : Space ι →L[ℂ] Space ι}
    (hA : A ∈ Algebra.adjoin ℂ (semicircular '' J)) (w : List ι)
    (hw : ∀ j ∈ w.head?, j ∉ J) :
    ∀ x ∈ wordSpace J,
      A x ∈ wordSpace J ∧ A (suffixEmbedding w x) = suffixEmbedding w (A x) := by
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
    obtain ⟨i, hi, rfl⟩ := hA
    exact fun x hx => ⟨semicircular_preserves_wordSpace hi hx, semicircular_suffix hi w hw hx⟩
  | algebraMap z =>
    intro x hx
    constructor
    · simpa using (wordSpace J).smul_mem z hx
    · simp
  | add A B _ _ hA hB =>
    intro x hx
    exact ⟨(wordSpace J).add_mem (hA x hx).1 (hB x hx).1,
      by simp only [add_apply, (hA x hx).2, (hB x hx).2, map_add]⟩
  | mul A B _ _ hA hB =>
    intro x hx
    exact ⟨(hA (B x) (hB x hx).1).1,
      by simp only [mul_apply_eq_comp, (hB x hx).2, (hA (B x) (hB x hx).1).2]⟩

 theorem centered_wordSpace_suffix {J : Set ι} {x : Space ι} (hx : x ∈ wordSpace J)
    (w : List ι) : suffixEmbedding w (x - x [] • basisVector []) ∈ startsIn J := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    cases v with
    | nil => simp [basisVector, lp.single_apply]
    | cons j v =>
      have hz : (basisVector (j :: v)) [] = 0 := by simp [basisVector, lp.single_apply]
      rw [hz, zero_smul, sub_zero, suffixEmbedding_basis]
      exact Submodule.subset_span ⟨j, hv j (by simp), v ++ w, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    have h : (x + y) - (x + y) [] • basisVector [] =
        (x - x [] • basisVector []) + (y - y [] • basisVector []) := by
      change (x + y) - (x [] + y []) • basisVector [] = _
      rw [add_smul]; abel
    rw [h, map_add]
    exact (startsIn J).add_mem hx hy
  | smul z x _ hx =>
    have h : z • x - (z • x) [] • basisVector [] =
        z • (x - x [] • basisVector []) := by
      change z • x - (z * x []) • basisVector [] = _
      rw [smul_sub, smul_smul]
    rw [h, map_smul]
    exact (startsIn J).smul_mem z hx

 theorem trace_eq_vacuum_coefficient (A : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) A = (A (basisVector [])) [] := by
  simp [trace, tracialVector, basisVector, lp.inner_single_left]

 theorem centered_adjoin_basis {J : Set ι} {A : Space ι →L[ℂ] Space ι}
    (hA : A ∈ Algebra.adjoin ℂ (semicircular '' J))
    (hcenter : trace (tracialVector ι) A = 0) (w : List ι)
    (hw : ∀ j ∈ w.head?, j ∉ J) : A (basisVector w) ∈ startsIn J := by
  have h := adjoin_suffix hA w hw (basisVector []) (vacuum_mem_wordSpace J)
  have hzero : (A (basisVector [])) [] = 0 := by
    rwa [← trace_eq_vacuum_coefficient]
  have hs := centered_wordSpace_suffix h.1 w
  simpa only [hzero, zero_smul, sub_zero, ← h.2, suffixEmbedding_basis, List.nil_append] using hs

 theorem centered_adjoin_startsIn {J K : Set ι} (hJK : Disjoint J K)
    {A : Space ι →L[ℂ] Space ι} (hA : A ∈ Algebra.adjoin ℂ (semicircular '' J))
    (hcenter : trace (tracialVector ι) A = 0) {x : Space ι} (hx : x ∈ startsIn K) :
    A x ∈ startsIn J := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, w, rfl⟩ := hx
    apply centered_adjoin_basis hA hcenter
    intro j hj hjJ
    have : j = i := by simpa using hj.symm
    subst j
    exact Set.disjoint_left.mp hJK hjJ hi
  | zero => simp
  | add x y _ _ hx hy => simpa using (startsIn J).add_mem hx hy
  | smul z x _ hx => simpa using (startsIn J).smul_mem z hx

 theorem startsIn_vacuum_zero {J : Set ι} {x : Space ι} (hx : x ∈ startsIn J) : x [] = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, _, w, rfl⟩ := hx
    simp [basisVector, lp.single_apply]
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul z x _ hx => simp [hx]

 theorem alternating_product_starts {κ : Type} (J : κ → Set ι)
    (hJ : Pairwise (fun i j => Disjoint (J i) (J j))) :
    ∀ (k : ℕ) (hk : 0 < k) (j : Fin k → κ) (a : Fin k → Space ι →L[ℂ] Space ι),
      (∀ r, a r ∈ Algebra.adjoin ℂ (semicircular '' J (j r))) →
      (∀ r, trace (tracialVector ι) (a r) = 0) →
      (∀ (r : ℕ) (hr : r + 1 < k),
        j ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩ ≠ j ⟨r + 1, hr⟩) →
      (List.ofFn a).prod (basisVector []) ∈ startsIn (J (j ⟨0, hk⟩)) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk j a ha hc hadj
    rw [List.ofFn_succ, List.prod_cons, mul_apply_eq_comp]
    cases k with
    | zero =>
      simpa using centered_adjoin_basis (ha 0) (hc 0) [] (by simp)
    | succ k =>
      have htail := ih (by omega) (fun r => j r.succ) (fun r => a r.succ)
        (fun r => ha r.succ) (fun r => hc r.succ) (by
          intro r hr
          exact hadj (r + 1) (by omega))
      exact centered_adjoin_startsIn (hJ (hadj 0 (by omega))) (ha 0) (hc 0) htail

theorem free_grouped_semicircular {κ : Type} (J : κ → Set ι)
    (hJ : Pairwise (fun i j => Disjoint (J i) (J j))) :
    FreeSubalgebras (tracialVector ι)
      (fun j => Algebra.adjoin ℂ (semicircular '' J j)) := by
  intro k hk j a ha hc hadj
  rw [trace_eq_vacuum_coefficient]
  exact startsIn_vacuum_zero (alternating_product_starts J hJ k hk j a ha hc hadj)

theorem free_semicircular :
    FreeSubalgebras (tracialVector ι) (fun i : ι => Algebra.adjoin ℂ {semicircular i}) := by
  simpa only [Set.image_singleton] using free_grouped_semicircular (fun i : ι => {i})
    (by intro i j hij; exact Set.disjoint_singleton.mpr hij)

theorem freeStandardNoise {m n : ℕ} (J : Set (Fin m))
    (X : Fin n → Space (Fin m) →L[ℂ] Space (Fin m))
    (hX : ∀ i, X i ∈ Algebra.adjoin ℂ (semicircular '' J))
    (σ : Fin n → Fin m) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    FreeStandardNoise (tracialVector (Fin m)) X (fun i => semicircular (σ i)) := by
  refine ⟨fun i k => semicircular_moments (σ i) k, ?_⟩
  let K : Option (Fin n) → Set (Fin m) := fun j => match j with
    | none => J
    | some i => {σ i}
  have hK : Pairwise (fun i j => Disjoint (K i) (K j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact Set.disjoint_singleton_right.mpr (hs j)
    | some i =>
      cases j with
      | none => exact Set.disjoint_singleton_left.mpr (hs i)
      | some j => exact Set.disjoint_singleton.mpr (fun h => hij (congrArg some (hσ h)))
  apply (free_grouped_semicircular K hK).mono
  intro j
  cases j with
  | none =>
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact hX i
  | some i => simp [K]

theorem rightAnnihilation_adjoin {J : Set ι} {i : ι} (hi : i ∉ J)
    {A : Space ι →L[ℂ] Space ι} (hA : A ∈ Algebra.adjoin ℂ (semicircular '' J)) :
    Commute (star (rightCreation i)) A := by
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
    obtain ⟨j, hj, rfl⟩ := hA
    have hij : i ≠ j := by intro h; subst j; exact hi hj
    show _ * _ = _ * _
    simpa [hij] using rightAnnihilation_semicircular i j
  | algebraMap z => exact Algebra.commutes z _ |>.symm
  | add A B _ _ hA hB => exact hA.add_right hB
  | mul A B _ _ hA hB => exact hA.mul_right hB

theorem heat_freeFisher_le {n : ℕ} (J : Set ι)
    (X : Fin n → Space ι →L[ℂ] Space ι)
    (hX : ∀ i, X i ∈ Algebra.adjoin ℂ (semicircular '' J))
    (σ : Fin n → ι) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 < u) :
    freeFisher (tracialVector ι) (heatTuple X (fun i => semicircular (σ i)) u) ≤
      ENNReal.ofReal ((n : ℝ) / u) := by
  let Z := heatTuple X (fun i => semicircular (σ i)) u
  let η : Fin n → Space ι := fun i => ((Real.sqrt u)⁻¹ : ℂ) • basisVector [σ i]
  have hc (i j : Fin n) : star (rightCreation (σ i)) * Z j =
      Z j * star (rightCreation (σ i)) +
        if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector ι) else 0 := by
    change _ * (X j + (Real.sqrt u : ℂ) • semicircular (σ j)) = _
    rw [mul_add, mul_smul_comm, (rightAnnihilation_adjoin (hs i) (hX j)).eq,
      rightAnnihilation_semicircular]
    change _ = (X j + (Real.sqrt u : ℂ) • semicircular (σ j)) *
      star (rightCreation (σ i)) +
      if j = i then (Real.sqrt u : ℂ) • vacuumProjection else 0
    by_cases hij : j = i
    · subst j
      simp only [ite_true, add_mul, smul_mul_assoc, add_assoc]
      congr 1
      exact smul_add _ _ _
    · have hneq : σ i ≠ σ j := fun h => hij (hσ h).symm
      simp [hij, hneq, add_mul, smul_mul_assoc]
  have hu' : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
  have hη (i : Fin n) (w : List (Fin n)) :
      inner ℂ (η i) (wordEval Z w (tracialVector ι).vacuum) =
        derivativeMoment (tracialVector ι) Z i w := by
    have h := commutator_integration_by_parts (tracialVector ι) Z
      (star (rightCreation (σ i))) i (Real.sqrt u) (hc i)
      (by simp [tracialVector, basisVector]) w
    simp only [star_star, tracialVector, basisVector, rightCreation_single,
      List.nil_append] at h
    change inner ℂ (((Real.sqrt u : ℂ)⁻¹) • lp.single 2 [σ i] 1)
      (wordEval Z w (lp.single 2 [] 1)) = _
    rw [inner_smul_left, h]
    simp [hu', tracialVector, basisVector]
  refine (freeFisher_le_testVectors (tracialVector ι) Z η hη).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hnorm (i : Fin n) : ‖η i‖ ^ 2 = u⁻¹ := by
    simp [η, norm_smul, basisVector, norm_inv,
      lp.norm_single (E := fun _ : List ι => ℂ) (p := 2),
      abs_of_nonneg (Real.sqrt_nonneg u), inv_pow, Real.sq_sqrt (le_of_lt hu)]
  simp [hnorm, div_eq_mul_inv]

end Fock

namespace LabelHilbert
open scoped lp
variable {α : Type} [DecidableEq α]
abbrev Space (α : Type) := lp (fun _ : α => ℂ) 2

def basis (a : α) : Space α := lp.single 2 a 1

def coordinateIsometry (a : α) : ℂ →ₗᵢ[ℂ] Space α where
  toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : α => ℂ) 2 a
  norm_map' z := lp.norm_single (E := fun _ : α => ℂ) (p := 2) (by norm_num) a z

theorem orthogonal_coordinates (f : α → α) (hf : Function.Injective f) :
    OrthogonalFamily ℂ (fun _ : α => ℂ) (fun a => coordinateIsometry (f a)) := by
  intro a b hab x y
  change inner ℂ (lp.single (E := fun _ : α => ℂ) 2 (f a) x)
    (lp.single (E := fun _ : α => ℂ) 2 (f b) y) = 0
  rw [lp.inner_single_left, lp.single_apply_ne (E := fun _ : α => ℂ) 2 (f b) y
    (fun h => hab (hf h))]
  simp

def lift (f : α → α) (hf : Function.Injective f) : Space α →L[ℂ] Space α :=
  (orthogonal_coordinates f hf).linearIsometry.toContinuousLinearMap

@[simp] theorem lift_single (f : α → α) (hf : Function.Injective f) (a : α) (z : ℂ) :
    lift f hf (lp.single 2 a z) = lp.single 2 (f a) z :=
  (orthogonal_coordinates f hf).linearIsometry_apply_single z

@[simp] theorem lift_basis (f : α → α) (hf : Function.Injective f) (a : α) :
    lift f hf (basis a) = basis (f a) := lift_single f hf a 1

 theorem adjoint_apply (f : α → α) (hf : Function.Injective f) (x : Space α) (a : α) :
    (star (lift f hf) x) a = x (f a) := by
  have h := ContinuousLinearMap.adjoint_inner_right (lift f hf) (basis a) x
  simpa [basis, ContinuousLinearMap.star_eq_adjoint, lp.inner_single_left] using h

 theorem adjoint_single_of_inverse (f : α → α) (hf : Function.Injective f)
    (q : α → Option α) (hq : ∀ a b, q b = some a ↔ f a = b) (b : α) (z : ℂ) :
    star (lift f hf) (lp.single 2 b z) = (q b).elim 0 (fun a => lp.single 2 a z) := by
  apply lp.ext
  funext a
  rw [adjoint_apply]
  cases h : q b with
  | none =>
    have hab : f a ≠ b := fun he => by have := (hq a b).mpr he; simp [h] at this
    simp [lp.single_apply, hab]
  | some c =>
    have hfc : f c = b := (hq c b).mp h
    subst b
    change (lp.single (E := fun _ : α => ℂ) 2 (f c) z) (f a) =
      (lp.single (E := fun _ : α => ℂ) 2 c z) a
    by_cases hac : a = c
    · subst a; simp
    · rw [lp.single_apply_ne (E := fun _ : α => ℂ) 2 (f c) z (fun h => hac (hf h)),
        lp.single_apply_ne (E := fun _ : α => ℂ) 2 c z hac]

 theorem lift_mul (f g : α → α) (hf : Function.Injective f) (hg : Function.Injective g) :
    lift f hf * lift g hg = lift (f ∘ g) (hf.comp hg) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro a
  apply ContinuousLinearMap.ext
  intro z
  change lift f hf (lift g hg (lp.single 2 a z)) = _
  simp

 theorem lift_commute (f g : α → α) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : Function.Commute f g) : Commute (lift f hf) (lift g hg) := by
  show _ * _ = _ * _
  rw [lift_mul, lift_mul]
  congr 1
  exact funext hfg

end LabelHilbert

namespace FreeTensor
variable {B N G : Type} [Group G]
abbrev Atom (B G : Type) := List B × G
abbrev Word (B N G : Type) := Atom B G × List (N × Atom B G)

def empty : Word B N G := (([], 1), [])
def push (a : Atom B G) (i : N) (w : Word B N G) : Word B N G :=
  (a, (i, w.1) :: w.2)
def append (w : Word B N G) (i : N) (a : Atom B G) : Word B N G :=
  (w.1, w.2 ++ [(i, a)])
def reverseAtom (a : Atom B G) : Atom B G := (a.1.reverse, a.2⁻¹)

@[simp] theorem reverseAtom_involutive (a : Atom B G) : reverseAtom (reverseAtom a) = a := by
  simp [reverseAtom]

def reverseAux (a : Atom B G) : List (N × Atom B G) → Word B N G
  | [] => (reverseAtom a, [])
  | (i,b) :: t => append (reverseAux b t) i (reverseAtom a)
def reverse (w : Word B N G) : Word B N G := reverseAux w.1 w.2

@[simp] theorem reverse_nil (a : Atom B G) : reverse (a, ([] : List (N × Atom B G))) =
    (reverseAtom a, []) := rfl
@[simp] theorem reverse_push (a : Atom B G) (i : N) (w : Word B N G) :
    reverse (push a i w) = append (reverse w) i (reverseAtom a) := rfl

omit [Group G] in
 theorem push_append (a b : Atom B G) (i j : N) (w : Word B N G) :
    push a i (append w j b) = append (push a i w) j b := rfl

 theorem reverse_append (w : Word B N G) (i : N) (a : Atom B G) :
    reverse (append w i a) = push (reverseAtom a) i (reverse w) := by
  rcases w with ⟨b, t⟩
  induction t generalizing b with
  | nil => rfl
  | cons c t ih =>
    rcases c with ⟨j,c⟩
    change append (reverse (append (c,t) i a)) j (reverseAtom b) = _
    rw [ih, ← push_append]
    rfl

@[simp] theorem reverse_involutive (w : Word B N G) : reverse (reverse w) = w := by
  rcases w with ⟨a,t⟩
  induction t generalizing a with
  | nil => simp
  | cons b t ih =>
    rcases b with ⟨i,b⟩
    change reverse (append (reverse (b,t)) i (reverseAtom a)) = _
    rw [reverse_append, reverseAtom_involutive, ih]
    rfl

def leftB (b : B) (w : Word B N G) : Word B N G := ((b :: w.1.1, w.1.2), w.2)
def leftN (i : N) (w : Word B N G) : Word B N G := push ([],1) i w
def leftG (g : G) (w : Word B N G) : Word B N G := ((w.1.1, g * w.1.2), w.2)
def rightB (b : B) (w : Word B N G) : Word B N G := reverse (leftB b (reverse w))
def rightN (i : N) (w : Word B N G) : Word B N G := reverse (leftN i (reverse w))
def rightG (g : G) (w : Word B N G) : Word B N G := reverse (leftG g (reverse w))

omit [Group G] in
 theorem leftB_injective (b : B) : Function.Injective (leftB (N := N) (G := G) b) := by
  rintro ⟨⟨v,g⟩,t⟩ ⟨⟨w,h⟩,s⟩ he
  simpa [leftB] using he
 theorem leftN_injective (i : N) : Function.Injective (leftN (B := B) (G := G) i) := by
  rintro ⟨a,t⟩ ⟨b,s⟩ he
  simpa [leftN, push] using he
 theorem leftG_injective (g : G) : Function.Injective (leftG (B := B) (N := N) g) := by
  rintro ⟨⟨v,h⟩,t⟩ ⟨⟨w,k⟩,s⟩ he
  simpa [leftG] using he
 theorem reverse_injective : Function.Injective (reverse (B := B) (N := N) (G := G)) :=
  Function.Involutive.injective reverse_involutive
 theorem rightB_injective (b : B) : Function.Injective (rightB (N := N) (G := G) b) :=
  reverse_injective.comp ((leftB_injective b).comp reverse_injective)
 theorem rightN_injective (i : N) : Function.Injective (rightN (B := B) (G := G) i) :=
  reverse_injective.comp ((leftN_injective i).comp reverse_injective)
 theorem rightG_injective (g : G) : Function.Injective (rightG (B := B) (N := N) g) :=
  reverse_injective.comp ((leftG_injective g).comp reverse_injective)

@[simp] theorem rightB_nil (b : B) (a : Atom B G) :
    rightB b (a, ([] : List (N × Atom B G))) = ((a.1 ++ [b],a.2),[]) := by
  simp [rightB, leftB, reverse, reverseAux, reverseAtom]
@[simp] theorem rightB_push (b : B) (a : Atom B G) (i : N) (w : Word B N G) :
    rightB b (push a i w) = push a i (rightB b w) := by
  have h (v : Word B N G) : leftB b (append v i (reverseAtom a)) =
      append (leftB b v) i (reverseAtom a) := rfl
  rw [rightB, reverse_push, h, reverse_append, reverseAtom_involutive]
  rfl
@[simp] theorem rightN_eq_append (i : N) (w : Word B N G) :
    rightN i w = append w i ([],1) := by
  rw [rightN, leftN, reverse_push, reverse_involutive]
  simp [reverseAtom]

@[simp] theorem rightG_nil (g : G) (a : Atom B G) :
    rightG g (a, ([] : List (N × Atom B G))) = ((a.1,a.2 * g⁻¹),[]) := by
  simp [rightG, leftG, reverse, reverseAux, reverseAtom]
@[simp] theorem rightG_push (g : G) (a : Atom B G) (i : N) (w : Word B N G) :
    rightG g (push a i w) = push a i (rightG g w) := by
  have h (v : Word B N G) : leftG g (append v i (reverseAtom a)) =
      append (leftG g v) i (reverseAtom a) := rfl
  rw [rightG, reverse_push, h, reverse_append, reverseAtom_involutive]
  rfl

 theorem leftB_rightB (b c : B) :
    Function.Commute (leftB (N := N) (G := G) b) (rightB c) := by
  rintro ⟨⟨v,g⟩,t⟩
  cases t with
  | nil => simp [leftB]
  | cons a t =>
    rcases a with ⟨i,a⟩
    change leftB b (rightB c (push (v,g) i (a,t))) =
      rightB c (push (b::v,g) i (a,t))
    rw [rightB_push, rightB_push]
    rfl
 theorem leftN_rightB (i : N) (b : B) :
    Function.Commute (leftN (G := G) i) (rightB b) := by
  intro w
  exact (rightB_push b ([],1) i w).symm
 theorem leftG_rightB (g : G) (b : B) :
    Function.Commute (leftG (N := N) g) (rightB b) := by
  rintro ⟨⟨v,h⟩,t⟩
  cases t with
  | nil => simp [leftG]
  | cons a t =>
    rcases a with ⟨i,a⟩
    change leftG g (rightB b (push (v,h) i (a,t))) =
      rightB b (push (v,g*h) i (a,t))
    rw [rightB_push, rightB_push]
    rfl
 theorem leftB_rightN (b : B) (i : N) :
    Function.Commute (leftB (G := G) b) (rightN i) := by
  intro w
  simp only [rightN_eq_append]
  rfl
 theorem leftN_rightN (i j : N) :
    Function.Commute (leftN (B := B) (G := G) i) (rightN j) := by
  intro w
  simp only [rightN_eq_append]
  rfl
 theorem leftG_rightN (g : G) (i : N) :
    Function.Commute (leftG (B := B) g) (rightN i) := by
  intro w
  simp only [rightN_eq_append]
  rfl
 theorem leftB_rightG (b : B) (g : G) :
    Function.Commute (leftB (N := N) b) (rightG g) := by
  rintro ⟨⟨v,h⟩,t⟩
  cases t with
  | nil => simp [leftB]
  | cons a t =>
    rcases a with ⟨i,a⟩
    change leftB b (rightG g (push (v,h) i (a,t))) =
      rightG g (push (b::v,h) i (a,t))
    rw [rightG_push, rightG_push]
    rfl
 theorem leftN_rightG (i : N) (g : G) :
    Function.Commute (leftN (B := B) i) (rightG g) := by
  intro w
  exact (rightG_push g ([],1) i w).symm
 theorem leftG_rightG (g h : G) :
    Function.Commute (leftG (B := B) (N := N) g) (rightG h) := by
  rintro ⟨⟨v,k⟩,t⟩
  cases t with
  | nil => simp [leftG, mul_assoc]
  | cons a t =>
    rcases a with ⟨i,a⟩
    change leftG g (rightG h (push (v,k) i (a,t))) =
      rightG h (push (v,g*k) i (a,t))
    rw [rightG_push, rightG_push]
    rfl

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]
open scoped lp
abbrev Space (B N G : Type) := LabelHilbert.Space (Word B N G)
def basis (w : Word B N G) : Space B N G := lp.single 2 w 1

def creationB (b : B) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (leftB b) (leftB_injective b)
def creationN (i : N) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (leftN i) (leftN_injective i)
def unitaryG (g : G) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (leftG g) (leftG_injective g)
def rightCreationB (b : B) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (rightB b) (rightB_injective b)
def rightCreationN (i : N) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (rightN i) (rightN_injective i)
def rightUnitaryG (g : G) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (rightG g) (rightG_injective g)

omit [Group G] in
@[simp] theorem creationB_single (b : B) (w : Word B N G) (z : ℂ) :
    creationB b (lp.single 2 w z) = lp.single 2 (leftB b w) z :=
  LabelHilbert.lift_single _ _ _ _
@[simp] theorem creationN_single (i : N) (w : Word B N G) (z : ℂ) :
    creationN i (lp.single 2 w z) = lp.single 2 (leftN i w) z :=
  LabelHilbert.lift_single _ _ _ _
@[simp] theorem unitaryG_single (g : G) (w : Word B N G) (z : ℂ) :
    unitaryG g (lp.single 2 w z) = lp.single 2 (leftG g w) z :=
  LabelHilbert.lift_single _ _ _ _
@[simp] theorem rightCreationB_single (b : B) (w : Word B N G) (z : ℂ) :
    rightCreationB b (lp.single 2 w z) = lp.single 2 (rightB b w) z :=
  LabelHilbert.lift_single _ _ _ _
@[simp] theorem rightCreationN_single (i : N) (w : Word B N G) (z : ℂ) :
    rightCreationN i (lp.single 2 w z) = lp.single 2 (rightN i w) z :=
  LabelHilbert.lift_single _ _ _ _
@[simp] theorem rightUnitaryG_single (g : G) (w : Word B N G) (z : ℂ) :
    rightUnitaryG g (lp.single 2 w z) = lp.single 2 (rightG g w) z :=
  LabelHilbert.lift_single _ _ _ _

def removeB (b : B) (w : Word B N G) : Option (Word B N G) :=
  match w.1.1 with
  | [] => none
  | c::v => if b = c then some ((v,w.1.2),w.2) else none

def removeN (i : N) (w : Word B N G) : Option (Word B N G) :=
  if w.1 = ([],1) then match w.2 with
    | [] => none
    | (j,a)::t => if i = j then some (a,t) else none
  else none

omit [Group G] [DecidableEq N] [DecidableEq G] in
 theorem removeB_spec (b : B) (u v : Word B N G) : removeB b v = some u ↔ leftB b u = v := by
  rcases u with ⟨⟨uv,ug⟩,ut⟩
  rcases v with ⟨⟨vv,vg⟩,vt⟩
  cases vv with
  | nil => simp [removeB, leftB]
  | cons c vv =>
    by_cases h : b = c
    · subst c; simp [removeB, leftB, eq_comm]
    · simp [removeB, leftB, h]

 theorem removeN_spec (i : N) (u v : Word B N G) : removeN i v = some u ↔ leftN i u = v := by
  rcases u with ⟨ua,ut⟩
  rcases v with ⟨va,vt⟩
  by_cases h : va = ([],1)
  · subst va
    cases vt with
    | nil => simp [removeN, leftN, push]
    | cons a t =>
      rcases a with ⟨j,a⟩
      by_cases hij : i = j
      · subst j; simp [removeN, leftN, push, eq_comm]
      · simp [removeN, leftN, push, hij]
  · simp [removeN, leftN, push, h, Ne.symm h]

omit [Group G] in
 theorem annihilationB_single (b : B) (w : Word B N G) (z : ℂ) :
    star (creationB b) (lp.single 2 w z) =
      (removeB b w).elim 0 (fun a => lp.single 2 a z) :=
  LabelHilbert.adjoint_single_of_inverse _ _ _ (removeB_spec b) _ _
 theorem annihilationN_single (i : N) (w : Word B N G) (z : ℂ) :
    star (creationN i) (lp.single 2 w z) =
      (removeN i w).elim 0 (fun a => lp.single 2 a z) :=
  LabelHilbert.adjoint_single_of_inverse _ _ _ (removeN_spec i) _ _

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
 theorem right_remove_spec (f : Word B N G → Word B N G)
    (q : Word B N G → Option (Word B N G)) (hq : ∀ u v, q v = some u ↔ f u = v)
    (u v : Word B N G) :
    (q (reverse v)).map reverse = some u ↔ reverse (f (reverse u)) = v := by
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨a,ha,hu⟩
    have had : a = reverse u := by rw [← hu, reverse_involutive]
    rw [had] at ha
    rw [(hq _ _).mp ha, reverse_involutive]
  · intro h
    refine ⟨reverse u, (hq _ _).mpr ?_, reverse_involutive u⟩
    have := congrArg reverse h
    simpa using this

 theorem rightAnnihilationB_single (b : B) (w : Word B N G) (z : ℂ) :
    star (rightCreationB b) (lp.single 2 w z) =
      ((removeB b (reverse w)).map reverse).elim 0 (fun a => lp.single 2 a z) :=
  LabelHilbert.adjoint_single_of_inverse _ _ _ (right_remove_spec _ _ (removeB_spec b)) _ _
 theorem rightAnnihilationN_single (i : N) (w : Word B N G) (z : ℂ) :
    star (rightCreationN i) (lp.single 2 w z) =
      ((removeN i (reverse w)).map reverse).elim 0 (fun a => lp.single 2 a z) :=
  LabelHilbert.adjoint_single_of_inverse _ _ _ (right_remove_spec _ _ (removeN_spec i)) _ _

@[simp] theorem rightAnnihilationN_atom (i : N) (a : Atom B G) (z : ℂ) :
    star (rightCreationN i) (lp.single 2 (a,[]) z) = 0 := by
  rw [rightAnnihilationN_single]
  have hr : removeN i (reverse (a,[])) = none := by
    dsimp only [reverse_nil, removeN]
    split <;> rfl
  rw [hr]
  rfl

 theorem rightAnnihilationN_append (i j : N) (w : Word B N G) (a : Atom B G) (z : ℂ) :
    star (rightCreationN i) (lp.single 2 (append w j a) z) =
      if a = ([],1) ∧ i = j then lp.single 2 w z else 0 := by
  rw [rightAnnihilationN_single, reverse_append]
  have ha : reverseAtom a = ([],1) ↔ a = ([],1) := by
    rcases a with ⟨v,g⟩
    simp [reverseAtom]
  by_cases haa : a = ([],1)
  · subst a
    by_cases hij : i = j <;> simp [removeN, push, reverseAtom, hij]
  · simp [removeN, push, ha, haa]

@[simp] theorem rightAnnihilationB_atom_nil (b : B) (g : G) (z : ℂ) :
    star (rightCreationB (N := N) b) (lp.single 2 (([],g),[]) z) = 0 := by
  rw [rightAnnihilationB_single]
  simp [reverse_nil, reverseAtom, removeB]

 theorem rightAnnihilationB_atom_append (b c : B) (v : List B) (g : G) (z : ℂ) :
    star (rightCreationB (N := N) b) (lp.single 2 ((v ++ [c],g),[]) z) =
      if b = c then lp.single 2 ((v,g),[]) z else 0 := by
  rw [rightAnnihilationB_single]
  by_cases h : b = c <;> simp [reverse_nil, reverseAtom, removeB, h]

@[simp] theorem rightAnnihilationB_append_nil (b : B) (w : Word B N G) (i : N)
    (g : G) (z : ℂ) :
    star (rightCreationB b) (lp.single 2 (append w i ([],g)) z) = 0 := by
  rw [rightAnnihilationB_single, reverse_append]
  simp [reverseAtom, push, removeB]

 theorem rightAnnihilationB_append_append (b c : B) (w : Word B N G) (i : N)
    (v : List B) (g : G) (z : ℂ) :
    star (rightCreationB b) (lp.single 2 (append w i (v ++ [c],g)) z) =
      if b = c then lp.single 2 (append w i (v,g)) z else 0 := by
  rw [rightAnnihilationB_single, reverse_append]
  have hinv := reverse_involutive w
  simp only [reverse] at hinv
  by_cases h : b = c <;>
    simp [reverseAtom, push, removeB, h, reverse, reverseAux, append, hinv]

 theorem creationB_commutes_rightAnnihilationN (b : B) (i : N) :
    Commute (creationB (G := G) b) (star (rightCreationN i)) := by
  show _ * _ = _ * _
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change creationB b (star (rightCreationN i) (lp.single 2 w z)) =
    star (rightCreationN i) (creationB b (lp.single 2 w z))
  rcases w with ⟨a,t⟩
  induction t using List.reverseRecOn with
  | nil => simp [leftB]
  | append_singleton t c _ =>
    rcases c with ⟨j,c⟩
    change creationB b (star (rightCreationN i) (lp.single 2 (append (a,t) j c) z)) = _
    rw [rightAnnihilationN_append, creationB_single]
    change creationB b (if c = ([],1) ∧ i = j then lp.single 2 (a,t) z else 0) =
      star (rightCreationN i) (lp.single 2 (append (leftB b (a,t)) j c) z)
    rw [rightAnnihilationN_append]
    split_ifs <;> simp

 theorem creationN_commutes_rightAnnihilationB (i : N) (b : B) :
    Commute (creationN (G := G) i) (star (rightCreationB b)) := by
  show _ * _ = _ * _
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change creationN i (star (rightCreationB b) (lp.single 2 w z)) =
    star (rightCreationB b) (creationN i (lp.single 2 w z))
  rcases w with ⟨⟨av,g⟩,t⟩
  induction t using List.reverseRecOn with
  | nil =>
    induction av using List.reverseRecOn with
    | nil =>
      rw [rightAnnihilationB_atom_nil, map_zero, creationN_single]
      change 0 = star (rightCreationB b) (lp.single 2 (append empty i ([],g)) z)
      simp
    | append_singleton v c _ =>
      rw [rightAnnihilationB_atom_append, creationN_single]
      change creationN i (if b = c then lp.single 2 ((v,g),[]) z else 0) =
        star (rightCreationB b) (lp.single 2 (append empty i (v ++ [c],g)) z)
      rw [rightAnnihilationB_append_append]
      split_ifs <;> simp [leftN, push, append, empty]
  | append_singleton t c _ =>
    rcases c with ⟨j,⟨v,h⟩⟩
    rw [creationN_single]
    change creationN i (star (rightCreationB b)
      (lp.single 2 (append ((av,g),t) j (v,h)) z)) =
      star (rightCreationB b) (lp.single 2 (append (leftN i ((av,g),t)) j (v,h)) z)
    induction v using List.reverseRecOn with
    | nil => simp
    | append_singleton v c _ =>
      rw [rightAnnihilationB_append_append, rightAnnihilationB_append_append]
      split_ifs <;> simp [leftN, push, append]

end FreeTensor

end FiniteEntropySeparation

end

end OAI
