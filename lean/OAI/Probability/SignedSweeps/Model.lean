import Mathlib

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

abbrev Partition (n : ℕ) := {lam : YoungDiagram // lam.card = n}

abbrev SymmetricGroup (n : ℕ) := Equiv.Perm (Fin n)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module

def transpose {n : ℕ} (lam : Partition n) : Partition n :=
  ⟨lam.1.transpose, by simpa [YoungDiagram.card, YoungDiagram.transpose] using lam.2⟩

def tableau {n : ℕ} (lam : Partition n) : {c // c ∈ lam.1.cells} ≃ Fin n :=
  Fintype.equivFinOfCardEq (by simpa using lam.2)

def rowOf {n : ℕ} (lam : Partition n) (x : Fin n) : ℕ :=
  ((tableau lam).symm x).1.1

def colOf {n : ℕ} (lam : Partition n) (x : Fin n) : ℕ :=
  ((tableau lam).symm x).1.2

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def fiberSubgroup {A C : Type*} (f : A → C) : Subgroup (Equiv.Perm A) where
  carrier := {g | ∀ x, f (g x) = f x}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro g h hg hh x
    exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    simpa using (hg (g⁻¹ x)).symm

def rowSubgroup {n : ℕ} (lam : Partition n) : Subgroup (SymmetricGroup n) :=
  fiberSubgroup lam.rowOf

def colSubgroup {n : ℕ} (lam : Partition n) : Subgroup (SymmetricGroup n) :=
  fiberSubgroup lam.colOf

abbrev RegularSpace (n : ℕ) := EuclideanSpace ℂ (SymmetricGroup n)

def regularIsometry {n : ℕ} (g : SymmetricGroup n) :
    RegularSpace n ≃ₗᵢ[ℂ] RegularSpace n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft g)

@[simp]
lemma regularIsometry_apply {n : ℕ} (g : SymmetricGroup n)
    (f : RegularSpace n) (h : SymmetricGroup n) :
    regularIsometry g f h = f (g⁻¹ * h) := rfl

def regularRepresentation (n : ℕ) : Representation ℂ (SymmetricGroup n) (RegularSpace n) where
  toFun g := (regularIsometry g).toLinearEquiv.toLinearMap
  map_one' := by ext f h; simp
  map_mul' := by
    intro g h
    ext f k
    simp [mul_assoc]

@[simp]
lemma regularRepresentation_apply {n : ℕ} (g : SymmetricGroup n)
    (f : RegularSpace n) (h : SymmetricGroup n) :
    regularRepresentation n g f h = f (g⁻¹ * h) := rfl

def polytabloid {n : ℕ} (lam : Partition n) : RegularSpace n := by
  classical
  exact ∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
    (((Equiv.Perm.sign (c : SymmetricGroup n) : ℤˣ) : ℤ) : ℂ) •
      EuclideanSpace.single ((c : SymmetricGroup n) * (a : SymmetricGroup n)) 1

def spechtSubrepresentation {n : ℕ} (lam : Partition n) :
    Subrepresentation (regularRepresentation n) where
  toSubmodule := Submodule.span ℂ (Set.range (fun g => regularRepresentation n g (polytabloid lam)))
  apply_mem_toSubmodule := by
    intro g f hf
    induction hf using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨h, rfl⟩ := hv
        apply Submodule.subset_span
        refine ⟨g * h, ?_⟩
        simp [map_mul, Module.End.mul_apply]
    | zero => simp
    | add x y hx hy ihx ihy =>
        simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
        simpa only [map_smul] using Submodule.smul_mem _ a ih

def Specht {n : ℕ} (lam : Partition n) : Type := (spechtSubrepresentation lam).toSubmodule

instance spechtNormedAddCommGroup {n : ℕ} (lam : Partition n) : NormedAddCommGroup (Specht lam) :=
  inferInstanceAs (NormedAddCommGroup (spechtSubrepresentation lam).toSubmodule)

instance spechtInnerProductSpace {n : ℕ} (lam : Partition n) : InnerProductSpace ℂ (Specht lam) :=
  inferInstanceAs (InnerProductSpace ℂ (spechtSubrepresentation lam).toSubmodule)

instance spechtFiniteDimensional {n : ℕ} (lam : Partition n) : FiniteDimensional ℂ (Specht lam) :=
  inferInstanceAs (FiniteDimensional ℂ (spechtSubrepresentation lam).toSubmodule)

def spechtRepresentation {n : ℕ} (lam : Partition n) :
    Representation ℂ (SymmetricGroup n) (Specht lam) :=
  (spechtSubrepresentation lam).toRepresentation

def spechtDimension {n : ℕ} (lam : Partition n) : ℕ := finrank ℂ (Specht lam)

def blockEmbedding {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (c : SymmetricGroup l) :
    SymmetricGroup n :=
  let e : (Fin u ⊕ Fin v) ⊕ Fin l ≃ Fin n :=
    ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin l))).trans finSumFinEquiv).trans
      (finCongr h)
  e.permCongr ((a.sumCongr b).sumCongr c)

def SignedOccurrence {u v l n : ℕ} (h : u + v + l = n)
    (α : Partition u) (β : Partition v) (γ : Partition l) (lam : Partition n) : Prop :=
  ∃ f : ((Specht α ⊗[ℂ] Specht β.transpose) ⊗[ℂ] Specht γ) →ₗ[ℂ] Specht lam,
    Function.Injective f ∧
    ∀ (a : SymmetricGroup u) (b : SymmetricGroup v) (c : SymmetricGroup l) x,
      f (TensorProduct.map
        (TensorProduct.map (spechtRepresentation α a) (spechtRepresentation β.transpose b))
        (spechtRepresentation γ c) x) =
      spechtRepresentation lam (blockEmbedding h a b c) (f x)

abbrev BinaryPositions (d : ℕ) := Fin d → Fin 2

def positionsEquiv (d : ℕ) : BinaryPositions d ≃ Fin (2 ^ d) :=
  Fintype.equivFinOfCardEq (by simp [BinaryPositions])

def coordinateSubgroup (d : ℕ) (i : Fin d) : Subgroup (SymmetricGroup (2 ^ d)) :=
  fiberSubgroup (fun x : Fin (2 ^ d) =>
    fun j : {j : Fin d // j ≠ i} => (positionsEquiv d).symm x j.1)

def layerOperator {d : ℕ} (lam : Partition (2 ^ d)) (i : Fin d) :
    Specht lam →ₗ[ℂ] Specht lam := by
  classical
  exact (Fintype.card (coordinateSubgroup d i) : ℂ)⁻¹ •
    ∑ g : coordinateSubgroup d i, spechtRepresentation lam g.1

def sweepOperator {d : ℕ} (lam : Partition (2 ^ d)) : Specht lam →ₗ[ℂ] Specht lam :=
  ((List.ofFn (layerOperator lam)).reverse).prod

def positiveSquare {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) : E →ₗ[ℂ] E := T.adjoint * T

def sweepSquare {d : ℕ} (lam : Partition (2 ^ d)) : Specht lam →ₗ[ℂ] Specht lam :=
  positiveSquare (E := Specht lam) (sweepOperator lam)

def weightedMoment {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) : ℝ :=
  (spechtDimension lam : ℝ) * (LinearMap.trace ℂ (Specht lam) (sweepSquare lam ^ r)).re

def logMoment (x : ℝ) : EReal := if x = 0 then ⊥ else (Real.log x : EReal)

def signedEntropy {u v : ℕ} (α : Partition u) (β : Partition v) : ℝ :=
  ((α.1.rowLens ++ β.1.rowLens).map
    (fun a : ℕ => (a : ℝ) * Real.log (((u : ℝ) + v) / a))).sum

def coefficient (a : ℝ) (d : ℕ) : ℝ := a * (1 - 1 / (2 * Real.sqrt d))

def remainderBudget (κ : ℝ) (d l : ℕ) : ℝ :=
  if l = 0 then 0 else
    max 0 (coefficient κ d * l * Real.log (2 ^ d : ℕ) -
      (l : ℝ) * Real.log ((2 ^ d : ℕ) / (l : ℝ)))

lemma positive_pow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsPositive) :
    ∀ r : ℕ, (T ^ r).IsPositive
  | 0 => LinearMap.isPositive_one
  | 1 => by simpa using hT
  | r + 2 => by
    have h := (positive_pow hT r).adjoint_conj T
    rw [hT.adjoint_eq] at h
    simpa only [← Module.End.mul_eq_comp, ← pow_succ', ← pow_succ] using h

lemma adjoint_mul_positive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) : (positiveSquare T).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self T

lemma sweepSquare_positive {d : ℕ} (lam : Partition (2 ^ d)) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Specht lam) (sweepSquare lam) := by
  exact adjoint_mul_positive (E := Specht lam) (sweepOperator lam)

lemma sweepSquare_pow_positive {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Specht lam) (sweepSquare lam ^ r) :=
  positive_pow (sweepSquare_positive lam) r

lemma sweepSquare_pow_trace_real {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    (LinearMap.trace ℂ (Specht lam) (sweepSquare lam ^ r)).im = 0 := by
  have h := (sweepSquare_pow_positive lam r).trace_nonneg
  exact (Complex.nonneg_iff.mp h).2.symm

lemma weightedMoment_nonneg {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    0 ≤ weightedMoment lam r := by
  have h := (sweepSquare_pow_positive lam r).trace_nonneg
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.nonneg_iff.mp h).1

lemma weightedMoment_zero_power {d : ℕ} (lam : Partition (2 ^ d)) :
    weightedMoment lam 0 = (spechtDimension lam : ℝ) ^ 2 := by
  simp [weightedMoment, LinearMap.trace_one, spechtDimension, pow_two]

@[simp]
lemma logMoment_zero : logMoment 0 = ⊥ := by simp [logMoment]

lemma logMoment_pos {x : ℝ} (hx : 0 < x) : logMoment x = (Real.log x : EReal) := by
  simp [logMoment, ne_of_gt hx]

lemma logMoment_le_iff {x y : ℝ} (hx : 0 ≤ x) :
    logMoment x ≤ (y : EReal) ↔ x ≤ Real.exp y := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x
    simp [logMoment, (Real.exp_pos y).le]
  · rw [logMoment_pos h, EReal.coe_le_coe_iff, Real.log_le_iff_le_exp h]

lemma row_part_le_size {n a : ℕ} (lam : Partition n) (ha : a ∈ lam.1.rowLens) : a ≤ n := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  rw [YoungDiagram.rowLen_eq_card]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2

lemma signedEntropy_nonneg {u v : ℕ} (α : Partition u) (β : Partition v) :
    0 ≤ signedEntropy α β := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have hp : 0 < a := by
    rcases List.mem_append.mp ha with ha | ha
    · exact α.1.pos_of_mem_rowLens _ ha
    · exact β.1.pos_of_mem_rowLens _ ha
  have hs : a ≤ u + v := by
    rcases List.mem_append.mp ha with ha | ha
    · exact (row_part_le_size α ha).trans (Nat.le_add_right _ _)
    · exact (row_part_le_size β ha).trans (Nat.le_add_left _ _)
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  rw [le_div_iff₀ (show (0 : ℝ) < a by exact_mod_cast hp), one_mul]
  exact_mod_cast hs

lemma signedEntropy_empty (α β : Partition 0) : signedEntropy α β = 0 := by
  have hα : α.1.rowLens = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have := row_part_le_size α ha
    have := α.1.pos_of_mem_rowLens a ha
    omega
  have hβ : β.1.rowLens = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have := row_part_le_size β ha
    have := β.1.pos_of_mem_rowLens a ha
    omega
  simp [signedEntropy, hα, hβ]

lemma coefficient_bounds {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 1 ≤ d) :
    a / 2 ≤ coefficient a d ∧ coefficient a d ≤ a := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 1 ≤ Real.sqrt d := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg d), Real.sqrt_nonneg (d : ℝ)]
  have hdiv : 0 ≤ 1 / (2 * Real.sqrt d) := by positivity
  have hdiv' : 1 / (2 * Real.sqrt d) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  constructor <;> unfold coefficient <;> nlinarith

lemma coefficient_nonneg {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ coefficient a d :=
  (div_nonneg ha (by norm_num)).trans (coefficient_bounds ha hd).1

@[simp]
lemma remainderBudget_zero (κ : ℝ) (d : ℕ) : remainderBudget κ d 0 = 0 := by
  simp [remainderBudget]

lemma remainderBudget_nonneg (κ : ℝ) (d l : ℕ) : 0 ≤ remainderBudget κ d l := by
  unfold remainderBudget
  split_ifs <;> simp

lemma entropy_angle_tradeoff {η F w : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) :
    -(1 - η) * w + min 0 (w - F) ≤ -(1 - η) * F := by
  by_cases h : w ≤ F
  · rw [min_eq_right (sub_nonpos.mpr h)]
    nlinarith [mul_nonneg hη (sub_nonneg.mpr h)]
  · have h' : F ≤ w := le_of_lt (lt_of_not_ge h)
    rw [min_eq_left (sub_nonneg.mpr h')]
    nlinarith [mul_nonneg (sub_nonneg.mpr hη') (sub_nonneg.mpr h')]

lemma spechtRepresentation_norm {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (x : Specht lam) : ‖spechtRepresentation lam g x‖ = ‖x‖ := by
  let x' : (spechtSubrepresentation lam).toSubmodule := x
  change ‖regularIsometry g (x' : RegularSpace n)‖ = ‖(x' : RegularSpace n)‖
  exact (regularIsometry g).norm_map _

lemma finite_average_contraction {I E : Type*} [Fintype I] [Nonempty I]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (A : I → E →ₗ[ℂ] E)
    (hA : ∀ i x, ‖A i x‖ ≤ ‖x‖) (x : E) :
    ‖((Fintype.card I : ℂ)⁻¹ • ∑ i, A i) x‖ ≤ ‖x‖ := by
  classical
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  calc
    ‖((Fintype.card I : ℂ)⁻¹ • ∑ i, A i) x‖ =
        (Fintype.card I : ℝ)⁻¹ * ‖∑ i, A i x‖ := by
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, norm_smul, norm_inv,
        Complex.norm_natCast]
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i, ‖A i x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ _ : I, ‖x‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hA i x)) (inv_nonneg.mpr hc.le)
    _ = ‖x‖ := by simp [ne_of_gt hc]

lemma layerOperator_contraction {d : ℕ} (lam : Partition (2 ^ d)) (i : Fin d)
    (x : Specht lam) : ‖layerOperator lam i x‖ ≤ ‖x‖ := by
  classical
  apply finite_average_contraction
  intro g y
  exact (spechtRepresentation_norm lam g.1 y).le

lemma list_prod_contraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : List (E →ₗ[ℂ] E)) (hL : ∀ A ∈ L, ∀ x, ‖A x‖ ≤ ‖x‖) (x : E) :
    ‖L.prod x‖ ≤ ‖x‖ := by
  induction L with
  | nil => simp
  | cons A L ih =>
    simp only [List.prod_cons, Module.End.mul_apply]
    exact (hL A (by simp) _).trans (ih (fun B hB y => hL B (by simp [hB]) y))

lemma sweepOperator_contraction {d : ℕ} (lam : Partition (2 ^ d)) (x : Specht lam) :
    ‖sweepOperator lam x‖ ≤ ‖x‖ := by
  apply list_prod_contraction
  intro A hA y
  simp only [List.mem_reverse, List.mem_ofFn] at hA
  obtain ⟨i, rfl⟩ := hA
  exact layerOperator_contraction lam i y

lemma adjoint_contraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) (x : E) :
    ‖T.adjoint x‖ ≤ ‖x‖ := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hnorm : ‖T.toContinuousLinearMap‖ ≤ 1 :=
    T.toContinuousLinearMap.opNorm_le_bound (by norm_num) (by simpa using hT)
  calc
    ‖T.adjoint x‖ ≤ ‖T.adjoint.toContinuousLinearMap‖ * ‖x‖ :=
      T.adjoint.toContinuousLinearMap.le_opNorm x
    _ = ‖T.toContinuousLinearMap‖ * ‖x‖ := by
      rw [LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖x‖ := one_mul _

lemma contraction_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) (r : ℕ) (x : E) :
    ‖(T ^ r) x‖ ≤ ‖x‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (hT _).trans ih

lemma sweepSquare_contraction {d : ℕ} (lam : Partition (2 ^ d)) (x : Specht lam) :
    ‖sweepSquare lam x‖ ≤ ‖x‖ := by
  change ‖(positiveSquare (sweepOperator lam)) x‖ ≤ ‖x‖
  exact (adjoint_contraction (sweepOperator lam) (sweepOperator_contraction lam) _).trans
    (sweepOperator_contraction lam x)

lemma contraction_trace_le_dim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) :
    (LinearMap.trace ℂ E T).re ≤ finrank ℂ E := by
  classical
  let b := stdOrthonormalBasis ℂ E
  have h : ∀ i, (inner ℂ (b i) (T (b i))).re ≤ 1 := by
    intro i
    calc
      (inner ℂ (b i) (T (b i))).re ≤ ‖inner ℂ (b i) (T (b i))‖ := Complex.re_le_norm _
      _ ≤ ‖b i‖ * ‖T (b i)‖ := norm_inner_le_norm _ _
      _ ≤ ‖b i‖ * ‖b i‖ := mul_le_mul_of_nonneg_left (hT _) (norm_nonneg _)
      _ = 1 := by simp only [b.norm_eq_one, one_mul]
  rw [LinearMap.trace_eq_sum_inner T b, Complex.re_sum]
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)

lemma weightedMoment_le_dimension_squared {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    weightedMoment lam r ≤ (spechtDimension lam : ℝ) ^ 2 := by
  unfold weightedMoment
  rw [pow_two]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact contraction_trace_le_dim _ (contraction_pow _ (sweepSquare_contraction lam) r)

lemma polytabloid_empty (lam : Partition 0) :
    polytabloid lam = EuclideanSpace.single (1 : SymmetricGroup 0) 1 := by
  classical
  let : Unique (rowSubgroup lam) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  let : Unique (colSubgroup lam) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  simp only [polytabloid, Fintype.sum_unique]
  rw [(Subsingleton.elim (default : colSubgroup lam) 1),
    (Subsingleton.elim (default : rowSubgroup lam) 1)]
  simp

lemma polytabloid_empty_ne_zero (lam : Partition 0) : polytabloid lam ≠ 0 := by
  classical
  intro he
  have h := congrArg (fun x : RegularSpace 0 => x (1 : SymmetricGroup 0)) he
  simp [polytabloid_empty lam] at h

lemma spechtSubrepresentation_empty (lam : Partition 0) :
    (spechtSubrepresentation lam).toSubmodule = Submodule.span ℂ {polytabloid lam} := by
  change Submodule.span ℂ _ = _
  congr 1
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have hg : g = 1 := Subsingleton.elim _ _
    simp [hg]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨1, by simp [hx]⟩

lemma spechtDimension_empty (lam : Partition 0) : spechtDimension lam = 1 := by
  change finrank ℂ (spechtSubrepresentation lam).toSubmodule = 1
  rw [spechtSubrepresentation_empty]
  exact finrank_span_singleton (polytabloid_empty_ne_zero lam)

end SignedSweeps
end

end OAI
