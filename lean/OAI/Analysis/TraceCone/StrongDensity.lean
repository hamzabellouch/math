import OAI.Analysis.Commutator.KaplanskySelfAdjoint
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

namespace OAI

/-!
# Strong density in operator algebras

Finite-vector bicommutant density, contractive Kaplansky approximation and
strong-star approximation in nonunital weak operator closures.
-/

noncomputable section
open scoped InnerProductSpace

namespace TraceConeClassification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev HilbertTuple (n : ℕ) (H : Type*) := Kadison.OperatorAmplification.SumSpace (H := H) (Fin n)

abbrev diagonalOp (n : ℕ) (T : H →L[ℂ] H) : HilbertTuple n H →L[ℂ] HilbertTuple n H :=
  Kadison.OperatorAmplification.diagonal (H := H) (Fin n) T

@[simp] lemma diagonalOp_apply (n : ℕ) (T : H →L[ℂ] H) (x : HilbertTuple n H) (i : Fin n) :
    diagonalOp n T x i = T (x i) := rfl

lemma diagonalOp_star (n : ℕ) (T : H →L[ℂ] H) :
    diagonalOp n (star T) = star (diagonalOp n T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, diagonalOp_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact T.adjoint_inner_left _ _

abbrev diagonalHom (n : ℕ) : (H →L[ℂ] H) →⋆ₐ[ℂ] (HilbertTuple n H →L[ℂ] HilbertTuple n H) :=
  Kadison.OperatorAmplification.diagonal (H := H) (Fin n)

abbrev tupleInclusion (n : ℕ) (j : Fin n) : H →L[ℂ] HilbertTuple n H :=
  Kadison.OperatorAmplification.single (H := H) (Fin n) j

omit [CompleteSpace H] in
@[simp] lemma tupleInclusion_apply (n : ℕ) (j : Fin n) (x : H) (i : Fin n) :
    tupleInclusion n j x i = if i = j then x else 0 := by
  simp [tupleInclusion]

omit [CompleteSpace H] in
lemma tuple_decomposition (n : ℕ) (x : HilbertTuple n H) :
    x = ∑ j, tupleInclusion n j (x j) := by
  ext i
  simp

lemma diagonalOp_inclusion (n : ℕ) (a : H →L[ℂ] H) (j : Fin n) (x : H) :
    diagonalOp n a (tupleInclusion n j x) = tupleInclusion n j (a x) := by
  ext i
  simp only [diagonalOp_apply, tupleInclusion_apply]
  split_ifs <;> simp

abbrev matrixEntry (n : ℕ) (R : HilbertTuple n H →L[ℂ] HilbertTuple n H) (i j : Fin n) : H →L[ℂ] H :=
  Kadison.OperatorAmplification.entry (H := H) (Fin n) R i j

omit [CompleteSpace H] in
@[simp] lemma matrixEntry_apply (n : ℕ) (R : HilbertTuple n H →L[ℂ] HilbertTuple n H)
    (i j : Fin n) (x : H) : matrixEntry n R i j x = R (tupleInclusion n j x) i := rfl

lemma diagonal_bicommutant (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) (n : ℕ) :
    diagonalHom (H := H) n T ∈ Set.centralizer
      (Set.centralizer ((A.map (diagonalHom (H := H) n)) : Set (HilbertTuple n H →L[ℂ] HilbertTuple n H))) := by
  exact Kadison.OperatorAmplification.diagonal_bicommutant (Fin n) A hT

/-- The finite-vector form of strong-operator density in the bicommutant. -/
theorem bicommutant_strong_density
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (n : ℕ) (ξ : Fin n → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, ∀ i, ‖a (ξ i) - T (ξ i)‖ < ε := by
  let x : HilbertTuple n H := WithLp.toLp 2 ξ
  obtain ⟨a, ha, he⟩ := Kadison.OperatorAmplification.bicommutant_finite_approx
    (Fin n) A hT x ε hε
  exact ⟨a, ha, fun i => (PiLp.norm_apply_le (diagonalOp n a x - diagonalOp n T x) i).trans_lt he⟩

open Filter Topology

lemma bicommutant_approximating_sequence
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (n : ℕ) (ξ : Fin n → H) :
    ∃ a : ℕ → H →L[ℂ] H, (∀ m, a m ∈ A) ∧
      ∀ i, Tendsto (fun m => a m (ξ i)) atTop (𝓝 (T (ξ i))) := by
  have hh (m : ℕ) : ∃ a ∈ A, ∀ i, ‖a (ξ i) - T (ξ i)‖ < 1 / ((m : ℝ) + 1) :=
    bicommutant_strong_density A T hT n ξ _ (by positivity)
  choose a ha he using hh
  refine ⟨a, ha, fun i => ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun m => dist_nonneg) (fun m => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [dist_eq_norm] using (he m i).le

/-- Self-adjoint strong density is needed before the contractive functional-calculus step. -/
theorem bicommutant_selfadjoint_strong_density
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) (n : ℕ) (ξ : Fin n → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, IsSelfAdjoint a ∧ ∀ i, ‖a (ξ i) - T (ξ i)‖ < ε := by
  let x : HilbertTuple n H := WithLp.toLp 2 ξ
  obtain ⟨a, ha, hsa_a, he⟩ := Kadison.Kaplansky.selfAdjoint_finite_approx
    (Fin n) A hT hsa x ε hε
  exact ⟨a, ha, hsa_a, fun i =>
    (PiLp.norm_apply_le (diagonalOp n a x - diagonalOp n T x) i).trans_lt he⟩

/-- Rational functions used to obtain bounded approximants without bounded input norms. -/
def densityG (t : ℝ) : ℝ := (1 + t^2)⁻¹
def densityH (t : ℝ) : ℝ := t / (1 + t^2)
def densityF (t : ℝ) : ℝ := 2 * densityH t
def densityK (t : ℝ) : ℝ := t / (1 + Real.sqrt (1 - t^2))

lemma density_den_pos (t : ℝ) : 0 < 1 + t^2 := by positivity
lemma densityG_cont : Continuous densityG := by
  exact (continuous_const.add (continuous_id.pow 2)).inv₀ (fun t => (density_den_pos t).ne')
lemma densityH_cont : Continuous densityH := by
  exact continuous_id.div (continuous_const.add (continuous_id.pow 2))
    (fun t => (density_den_pos t).ne')
lemma densityF_cont : Continuous densityF := continuous_const.mul densityH_cont
lemma densityK_cont : Continuous densityK := by
  exact continuous_id.div (continuous_const.add
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))))
    (fun t => (by positivity : (1 : ℝ) + Real.sqrt (1 - t^2) ≠ 0))

lemma densityG_bound (t : ℝ) : ‖densityG t‖ ≤ 1 := by
  rw [densityG, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (density_den_pos t))]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])
lemma densityH_bound (t : ℝ) : ‖densityH t‖ ≤ 1 / 2 := by
  rw [densityH, Real.norm_eq_abs, abs_div, abs_of_pos (density_den_pos t)]
  apply (div_le_iff₀ (density_den_pos t)).mpr
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]
lemma densityF_bound (t : ℝ) : ‖densityF t‖ ≤ 1 := by
  have hh := densityH_bound t
  rw [Real.norm_eq_abs] at hh
  rw [densityF, norm_mul]
  norm_num
  linarith
lemma density_FK (t : ℝ) (ht : |t| ≤ 1) : densityF (densityK t) = t := by
  have hsq : 0 ≤ 1 - t^2 := by nlinarith [sq_abs t, abs_nonneg t]
  have hs := Real.sq_sqrt hsq
  have hd : 1 + Real.sqrt (1 - t^2) ≠ 0 := by positivity
  have hd' := (density_den_pos (densityK t)).ne'
  dsimp [densityF, densityH, densityK] at hd' ⊢
  field_simp
  linear_combination -t * hs

section RationalOperators
variable {B : Type*} [CStarAlgebra B]

def densityg (a : B) : B := cfc densityG a
def densityh (a : B) : B := cfc densityH a
def densityf (a : B) : B := cfc densityF a

lemma densityg_norm (a : B) : ‖densityg a‖ ≤ 1 :=
  norm_cfc_le zero_le_one (fun t _ => densityG_bound t)
lemma densityh_norm (a : B) : ‖densityh a‖ ≤ 1 :=
  (norm_cfc_le (by norm_num : (0:ℝ) ≤ 1/2) (fun t _ => densityH_bound t)).trans (by norm_num)
lemma densityf_norm (a : B) : ‖densityf a‖ ≤ 1 :=
  norm_cfc_le zero_le_one (fun t _ => densityF_bound t)
lemma densityf_eq (a : B) : densityf a = (2:ℝ) • densityh a := by
  exact cfc_const_mul 2 densityH a densityH_cont.continuousOn
lemma density_selfadjoint (a : B) : IsSelfAdjoint (densityf a) := IsSelfAdjoint.cfc

lemma densityg_mul (a : B) (ha : IsSelfAdjoint a) : densityg a * a = densityh a := by
  change cfc densityG a * a = cfc densityH a
  conv_lhs => rhs; rw [← cfc_id ℝ a ha]
  rw [← cfc_mul densityG id a
    densityG_cont.continuousOn continuous_id.continuousOn]
  apply cfc_congr
  intro t _
  simp [densityG, densityH, div_eq_mul_inv, mul_comm]
lemma mul_densityg (a : B) (ha : IsSelfAdjoint a) : a * densityg a = densityh a := by
  calc
    a * densityg a = densityg a * a := (Commute.refl a |>.cfc_real densityG).eq.symm
    _ = densityh a := densityg_mul a ha
lemma densityh_mul (a : B) (ha : IsSelfAdjoint a) : densityh a * a = 1 - densityg a := by
  change cfc densityH a * a = 1 - densityg a
  conv_lhs => rhs; rw [← cfc_id ℝ a ha]
  rw [← cfc_mul densityH id a
    densityH_cont.continuousOn continuous_id.continuousOn]
  rw [← cfc_const_one ℝ a ha, densityg,
    ← cfc_sub (fun _ : ℝ => 1) densityG a continuous_const.continuousOn densityG_cont.continuousOn]
  apply cfc_congr
  intro t _
  dsimp [densityH, densityG]
  field_simp
  ring
lemma mul_densityh (a : B) (ha : IsSelfAdjoint a) : a * densityh a = 1 - densityg a := by
  calc
    a * densityh a = densityh a * a := (Commute.refl a |>.cfc_real densityH).eq.symm
    _ = 1 - densityg a := densityh_mul a ha

lemma densityh_difference (a b : B) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    densityh a - densityh b =
      densityg a * (a - b) * densityg b - densityh a * (a - b) * densityh b := by
  rw [mul_sub, sub_mul, mul_sub, sub_mul, densityg_mul a ha,
    mul_assoc (densityg a), mul_densityg b hb,
    densityh_mul a ha, mul_assoc (densityh a), mul_densityh b hb]
  noncomm_ring
end RationalOperators


lemma density_FK_operator {B : Type*} [CStarAlgebra B] (T : B)
    (hsa : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1) :
    densityf (cfc densityK T) = T := by
  rcases subsingleton_or_nontrivial B with h | h
  · exact Subsingleton.elim _ _
  rw [densityf, ← cfc_comp densityF densityK T hsa
    densityF_cont.continuousOn densityK_cont.continuousOn]
  calc
    cfc (densityF ∘ densityK) T = cfc id T := by
      apply cfc_congr
      intro t ht
      apply density_FK
      exact (spectrum.norm_le_norm_of_mem ht).trans hnorm
    _ = T := cfc_id ℝ T hsa

lemma densityh_apply_difference (a b : H →L[ℂ] H) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (ξ : H) :
    ‖densityh a ξ - densityh b ξ‖ ≤
      ‖a (densityg b ξ) - b (densityg b ξ)‖ +
      ‖a (densityh b ξ) - b (densityh b ξ)‖ := by
  have hid := congrArg (fun f : H →L[ℂ] H => f ξ) (densityh_difference a b ha hb)
  simp only [sub_apply, mul_apply_eq_comp] at hid
  rw [hid]
  calc
    _ ≤ ‖densityg a (a (densityg b ξ) - b (densityg b ξ))‖ +
        ‖densityh a (a (densityh b ξ) - b (densityh b ξ))‖ := norm_sub_le _ _
    _ ≤ ‖a (densityg b ξ) - b (densityg b ξ)‖ +
        ‖a (densityh b ξ) - b (densityh b ξ)‖ := by
      apply add_le_add
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (by simpa using mul_le_mul_of_nonneg_right (densityg_norm a) (norm_nonneg _))
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (by simpa using mul_le_mul_of_nonneg_right (densityh_norm a) (norm_nonneg _))

/-- Contractive self-adjoint Kaplansky approximation, with actual construction
from the double commutant and no bound assumed on the initial approximants. -/
theorem kaplansky_selfadjoint
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hclosed : IsClosed (A : Set (H →L[ℂ] H)))
    (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1)
    (n : ℕ) (ξ : Fin n → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧ ∀ i, ‖a (ξ i) - T (ξ i)‖ < ε := by
  let b := cfc densityK T
  have hb : IsSelfAdjoint b := IsSelfAdjoint.cfc
  have hbcomm : b ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    intro S hS
    have hc : Commute T S := (hT S hS).symm
    exact (hc.cfc_real densityK).eq.symm
  have hFb : densityf b = T := density_FK_operator T hsa hnorm
  obtain ⟨a, ha, hsa_a, he⟩ := bicommutant_selfadjoint_strong_density A b hbcomm hb (n+n)
    (Fin.addCases (fun i => densityg b (ξ i)) (fun i => densityh b (ξ i)))
    (ε/4) (by positivity)
  have : IsClosed (A : Set (H →L[ℂ] H)) := hclosed
  refine ⟨densityf a, cfc_mem (𝕜' := ℂ) densityF ha, density_selfadjoint a,
    densityf_norm a, fun i => ?_⟩
  have he₁ : ‖a (densityg b (ξ i)) - b (densityg b (ξ i))‖ < ε/4 := by
    simpa only [Fin.addCases_left] using he (Fin.castAdd n i)
  have he₂ : ‖a (densityh b (ξ i)) - b (densityh b (ξ i))‖ < ε/4 := by
    simpa only [Fin.addCases_right] using he (Fin.natAdd n i)
  rw [← hFb, densityf_eq, densityf_eq]
  simp only [smul_apply, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hh := densityh_apply_difference a b hsa_a hb (ξ i)
  linarith


omit [CompleteSpace H] in
lemma tuple_inner_inclusion (n : ℕ) (i : Fin n) (x : H) (y : HilbertTuple n H) :
    inner ℂ (tupleInclusion n i x) y = inner ℂ x (y i) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · simp
omit [CompleteSpace H] in
lemma tuple_inclusion_inner (n : ℕ) (i : Fin n) (x : H) (y : HilbertTuple n H) :
    inner ℂ y (tupleInclusion n i x) = inner ℂ (y i) x := by
  simp [PiLp.inner_apply, apply_ite]
omit [CompleteSpace H] in
lemma tuple_inclusion_norm (n : ℕ) (i : Fin n) (x : H) :
    ‖tupleInclusion n i x‖ = ‖x‖ := by
  change ‖PiLp.single (β := fun _ : Fin n => H) 2 i x‖ = ‖x‖
  exact PiLp.norm_single 2 (fun _ : Fin n => H) i x

lemma matrixEntry_star (n : ℕ) (R : HilbertTuple n H →L[ℂ] HilbertTuple n H) (i j : Fin n) :
    matrixEntry n (star R) i j = star (matrixEntry n R j i) := by
  ext x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (matrixEntry n (star R) i j x) y =
    inner ℂ ((matrixEntry n R j i).adjoint x) y
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star R (tupleInclusion n j x) i) y =
    inner ℂ x (R (tupleInclusion n i y) j)
  rw [← tuple_inclusion_inner, ← tuple_inner_inclusion]
  exact ContinuousLinearMap.adjoint_inner_left R _ _

omit [CompleteSpace H] in
lemma matrixEntry_norm (n : ℕ) (R : HilbertTuple n H →L[ℂ] HilbertTuple n H) (i j : Fin n) :
    ‖matrixEntry n R i j‖ ≤ ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
  intro x
  calc
    _ ≤ ‖R (tupleInclusion n j x)‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖R‖ * ‖tupleInclusion n j x‖ := R.le_opNorm _
    _ = ‖R‖ * ‖x‖ := by rw [tuple_inclusion_norm]

omit [CompleteSpace H] in
lemma matrixEntry_continuous (n : ℕ) (i j : Fin n) :
    Continuous (fun R : HilbertTuple n H →L[ℂ] HilbertTuple n H => matrixEntry n R i j) := by
  unfold matrixEntry Kadison.OperatorAmplification.entry
  fun_prop

omit [CompleteSpace H] in
@[simp] lemma matrixEntry_zero (n : ℕ) (i j : Fin n) :
    matrixEntry n (0 : HilbertTuple n H →L[ℂ] HilbertTuple n H) i j = 0 := by ext x; rfl
omit [CompleteSpace H] in
@[simp] lemma matrixEntry_add (n : ℕ) (R S : HilbertTuple n H →L[ℂ] HilbertTuple n H)
    (i j : Fin n) : matrixEntry n (R + S) i j = matrixEntry n R i j + matrixEntry n S i j := by ext x; rfl
omit [CompleteSpace H] in
@[simp] lemma matrixEntry_smul (n : ℕ) (r : ℂ) (R : HilbertTuple n H →L[ℂ] HilbertTuple n H)
    (i j : Fin n) : matrixEntry n (r • R) i j = r • matrixEntry n R i j := by ext x; rfl
omit [CompleteSpace H] in
@[simp] lemma matrixEntry_one (n : ℕ) (i j : Fin n) :
    matrixEntry n (1 : HilbertTuple n H →L[ℂ] HilbertTuple n H) i j = if i = j then 1 else 0 := by
  ext x
  by_cases h : i = j <;> simp [h]

omit [CompleteSpace H] in
lemma matrixEntry_mul (n : ℕ) (R S : HilbertTuple n H →L[ℂ] HilbertTuple n H)
    (i j : Fin n) : matrixEntry n (R * S) i j = ∑ k, matrixEntry n R i k * matrixEntry n S k j := by
  ext x
  have hh := congrArg (fun y => R y i) (tuple_decomposition n (S (tupleInclusion n j x)))
  simpa only [map_sum, WithLp.ofLp_sum, Finset.sum_apply, matrixEntry_apply,
    mul_apply_eq_comp, sum_apply] using hh

@[simp] lemma matrixEntry_diagonal (n : ℕ) (a : H →L[ℂ] H) (i j : Fin n) :
    matrixEntry n (diagonalOp n a) i j = if i = j then a else 0 := by
  ext x
  by_cases h : i = j <;> simp [diagonalOp_inclusion, h]

def matrixSubalgebra (n : ℕ) (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (HilbertTuple n H →L[ℂ] HilbertTuple n H) where
  carrier := {R | ∀ i j, matrixEntry n R i j ∈ A}
  zero_mem' := by intro i j; simp
  one_mem' := by intro i j; simp only [matrixEntry_one]; split_ifs <;> simp
  add_mem' hR hS := by intro i j; simpa using A.add_mem (hR i j) (hS i j)
  mul_mem' hR hS := by
    intro i j
    rw [matrixEntry_mul]
    exact A.sum_mem (fun k _ => A.mul_mem (hR i k) (hS k j))
  algebraMap_mem' r := by
    intro i j
    rw [Algebra.algebraMap_eq_smul_one, matrixEntry_smul]
    exact A.smul_mem (by rw [matrixEntry_one]; split_ifs <;> simp) r
  star_mem' hR := by
    intro i j
    rw [matrixEntry_star]
    exact A.star_mem' (hR j i)

lemma matrixSubalgebra_closed (n : ℕ) (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsClosed (A : Set (H →L[ℂ] H))) : IsClosed (matrixSubalgebra n A : Set (HilbertTuple n H →L[ℂ] HilbertTuple n H)) := by
  change IsClosed {R | ∀ i j, matrixEntry n R i j ∈ A}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_iInter (fun j => hA.preimage (matrixEntry_continuous n i j)))

lemma diagonal_mem_matrixSubalgebra (n : ℕ) (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (a : H →L[ℂ] H) (ha : a ∈ A) : diagonalOp n a ∈ matrixSubalgebra n A := by
  intro i j
  rw [matrixEntry_diagonal]
  split_ifs <;> simp_all

lemma diagonal_matrix_bicommutant (n : ℕ) (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) :
    diagonalOp n T ∈ Set.centralizer (Set.centralizer (matrixSubalgebra n A : Set (HilbertTuple n H →L[ℂ] HilbertTuple n H))) := by
  apply Set.centralizer_subset (Set.centralizer_subset ?_) (diagonal_bicommutant A T hT n)
  intro R hR
  obtain ⟨a, ha, rfl⟩ := StarSubalgebra.mem_map.mp hR
  exact diagonal_mem_matrixSubalgebra n A a ha


def blockOp (n : ℕ) (i j : Fin n) (T : H →L[ℂ] H) : HilbertTuple n H →L[ℂ] HilbertTuple n H :=
  (tupleInclusion n i).comp (T.comp (PiLp.proj 2 (fun _ : Fin n => H) j))

omit [CompleteSpace H] in
@[simp] lemma blockOp_apply (n : ℕ) (i j : Fin n) (T : H →L[ℂ] H)
    (x : HilbertTuple n H) (k : Fin n) : blockOp n i j T x k = if k = i then T (x j) else 0 :=
  tupleInclusion_apply n i (T (x j)) k

lemma blockOp_star (n : ℕ) (i j : Fin n) (T : H →L[ℂ] H) :
    star (blockOp n i j T) = blockOp n j i (star T) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (tupleInclusion n i (T (x j))) y =
    inner ℂ x (tupleInclusion n j (star T (y i)))
  rw [tuple_inner_inclusion, tuple_inclusion_inner]
  exact (ContinuousLinearMap.adjoint_inner_right T _ _).symm

omit [CompleteSpace H] in
@[simp] lemma matrixEntry_blockOp (n : ℕ) (i j k l : Fin n) (T : H →L[ℂ] H) :
    matrixEntry n (blockOp n i j T) k l = if k = i ∧ l = j then T else 0 := by
  by_cases hk : k = i <;> by_cases hl : l = j
  · subst k; subst l; ext x; simp [blockOp_apply]
  · ext x; simp [blockOp_apply, hk, hl, Ne.symm hl]
  · ext x; simp [blockOp_apply, hk, hl]
  · ext x; simp [blockOp_apply, hk, hl]

lemma blockOp_mem_matrixSubalgebra (n : ℕ) (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (i j : Fin n) (T : H →L[ℂ] H) (hT : T ∈ A) : blockOp n i j T ∈ matrixSubalgebra n A := by
  intro k l
  rw [matrixEntry_blockOp]
  split_ifs <;> simp_all

lemma blockOp_eq_diagonal (n : ℕ) (i j : Fin n) (T : H →L[ℂ] H) :
    blockOp n i j T = diagonalOp n T * blockOp n i j 1 := by
  ext x k
  simp only [blockOp_apply, mul_apply_eq_comp, diagonalOp_apply]
  split_ifs <;> simp

def offDiagonalOp (T : H →L[ℂ] H) : HilbertTuple 2 H →L[ℂ] HilbertTuple 2 H :=
  blockOp 2 0 1 T + star (blockOp 2 0 1 T)

lemma offDiagonal_selfadjoint (T : H →L[ℂ] H) : IsSelfAdjoint (offDiagonalOp T) := by
  change IsSelfAdjoint (blockOp 2 0 1 T + star (blockOp 2 0 1 T))
  exact IsSelfAdjoint.add_star_self (blockOp 2 0 1 T)

@[simp] lemma offDiagonal_apply_zero (T : H →L[ℂ] H) (x : HilbertTuple 2 H) :
    offDiagonalOp T x 0 = T (x 1) := by simp [offDiagonalOp, blockOp_star]
@[simp] lemma offDiagonal_apply_one (T : H →L[ℂ] H) (x : HilbertTuple 2 H) :
    offDiagonalOp T x 1 = star T (x 0) := by simp [offDiagonalOp, blockOp_star]

lemma offDiagonal_norm (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) : ‖offDiagonalOp T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul]
  have h₁ : ‖T (x 1)‖ ≤ ‖x 1‖ := (T.le_opNorm _).trans (by nlinarith [norm_nonneg (x 1)])
  have h₂ : ‖star T (x 0)‖ ≤ ‖x 0‖ := (ContinuousLinearMap.le_opNorm _ _).trans
    (by rw [norm_star]; nlinarith [norm_nonneg (x 0)])
  have hn : ‖offDiagonalOp T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_two, offDiagonal_apply_zero, offDiagonal_apply_one]
    nlinarith [norm_nonneg (T (x 1)), norm_nonneg (star T (x 0)), norm_nonneg (x 0), norm_nonneg (x 1)]
  nlinarith [norm_nonneg (offDiagonalOp T x), norm_nonneg x]

lemma offDiagonal_bicommutant (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) :
    offDiagonalOp T ∈ Set.centralizer (Set.centralizer
      (matrixSubalgebra 2 A : Set (HilbertTuple 2 H →L[ℂ] HilbertTuple 2 H))) := by
  let D := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
    (matrixSubalgebra 2 A : Set (HilbertTuple 2 H →L[ℂ] HilbertTuple 2 H)) :
      Set (HilbertTuple 2 H →L[ℂ] HilbertTuple 2 H))
  have hD : (D : Set (HilbertTuple 2 H →L[ℂ] HilbertTuple 2 H)) =
      Set.centralizer (Set.centralizer (matrixSubalgebra 2 A :
        Set (HilbertTuple 2 H →L[ℂ] HilbertTuple 2 H))) := by
    simp only [D, StarSubalgebra.coe_centralizer_centralizer, StarMemClass.star_coe_eq, Set.union_self]
  have hd : diagonalOp 2 T ∈ D := by
    rw [← SetLike.mem_coe, hD]
    exact diagonal_matrix_bicommutant 2 A T hT
  have hu : blockOp 2 0 1 (1 : H →L[ℂ] H) ∈ D := by
    rw [← SetLike.mem_coe, hD]
    exact Set.subset_centralizer_centralizer (blockOp_mem_matrixSubalgebra 2 A 0 1 1 A.one_mem)
  have hb : blockOp 2 0 1 T ∈ D := by
    rw [blockOp_eq_diagonal]
    exact D.mul_mem hd hu
  rw [← hD]
  exact D.add_mem hb (D.star_mem' hb)


/-- Contractive strong-star density obtained by self-adjoint matrix amplification. -/
theorem kaplansky_strong_star
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hclosed : IsClosed (A : Set (H →L[ℂ] H)))
    (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hnorm : ‖T‖ ≤ 1) (n : ℕ) (ξ : Fin n → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, ‖a‖ ≤ 1 ∧ ∀ i,
      ‖a (ξ i) - T (ξ i)‖ < ε ∧ ‖star a (ξ i) - star T (ξ i)‖ < ε := by
  obtain ⟨R, hR, hsa, hnormR, he⟩ := kaplansky_selfadjoint
    (matrixSubalgebra 2 A) (matrixSubalgebra_closed 2 A hclosed) (offDiagonalOp T)
    (offDiagonal_bicommutant A T hT) (offDiagonal_selfadjoint T) (offDiagonal_norm T hnorm)
    (n+n) (Fin.addCases (fun i => tupleInclusion 2 1 (ξ i))
      (fun i => tupleInclusion 2 0 (ξ i))) ε hε
  refine ⟨matrixEntry 2 R 0 1, hR 0 1, (matrixEntry_norm 2 R 0 1).trans hnormR, fun i => ?_⟩
  have he₁ : ‖R (tupleInclusion 2 1 (ξ i)) - offDiagonalOp T (tupleInclusion 2 1 (ξ i))‖ < ε := by
    simpa only [Fin.addCases_left] using he (Fin.castAdd n i)
  have he₂ : ‖R (tupleInclusion 2 0 (ξ i)) - offDiagonalOp T (tupleInclusion 2 0 (ξ i))‖ < ε := by
    simpa only [Fin.addCases_right] using he (Fin.natAdd n i)
  constructor
  · have hh := (PiLp.norm_apply_le
      (R (tupleInclusion 2 1 (ξ i)) - offDiagonalOp T (tupleInclusion 2 1 (ξ i))) (0:Fin 2)).trans_lt he₁
    simpa [matrixEntry_apply] using hh
  · rw [← matrixEntry_star, hsa.star_eq]
    have hh := (PiLp.norm_apply_le
      (R (tupleInclusion 2 0 (ξ i)) - offDiagonalOp T (tupleInclusion 2 0 (ξ i))) (1:Fin 2)).trans_lt he₂
    simpa [matrixEntry_apply] using hh

def ofWOTHom : (H →L[ℂ] H) →⋆ₙₐ[ℂ] (H →WOT[ℂ] H) where
  toFun := ContinuousLinearMapWOT.ofCLM
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

def weakClosure (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) :=
  ((A.map ofWOTHom).topologicalClosure).comap ofWOTHom

lemma weakClosure_mem (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    T ∈ weakClosure A ↔ ContinuousLinearMapWOT.ofCLM T ∈ closure
      (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[ℂ] H))) := Iff.rfl

lemma weakClosure_closed (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed (weakClosure A : Set (H →L[ℂ] H)) :=
  isClosed_closure.preimage ContinuousLinearMapWOT.continuous_ofCLM

lemma weakClosure_cfc (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ weakClosure A) (f : ℝ → ℝ) (hf : f 0 = 0) (hcont : Continuous f) : cfc f T ∈ weakClosure A := by
  have := weakClosure_closed A
  rw [← cfcₙ_eq_cfc (f := f) (a := T) hcont.continuousOn hf]
  exact cfcₙ_mem (𝕜' := ℂ) f hT

def nonunitalSelfAdjointOrbit (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (n : ℕ) (ξ : HilbertTuple n H) : selfAdjoint A →ₗ[ℝ] HilbertTuple n H where
  toFun a := diagonalOp n (a.val.val) ξ
  map_add' a b := by ext i; rfl
  map_smul' r a := by ext i; rfl

lemma weakClosure_selfadjoint_orthogonal
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ weakClosure A) (hsa : IsSelfAdjoint T) (n : ℕ) (ξ η : HilbertTuple n H)
    (horth : ∀ a ∈ A, IsSelfAdjoint a → (inner ℂ (diagonalOp n a ξ) η).re = 0) :
    (inner ℂ (diagonalOp n T ξ) η).re = 0 := by
  let F : (H →WOT[ℂ] H) → ℝ := fun a =>
    ∑ i, ((inner ℂ (a (ξ i)) (η i)).re + (inner ℂ (ξ i) (a (η i))).re)
  have hc : Continuous F := by
    apply continuous_finsetSum
    intro i _
    apply Continuous.add
    · have heq (a : H →WOT[ℂ] H) : (inner ℂ (a (ξ i)) (η i)).re = (inner ℂ (η i) (a (ξ i))).re := inner_re_symm (𝕜 := ℂ) _ _
      simp_rw [heq]
      exact Complex.continuous_re.comp (ContinuousLinearMapWOT.continuous_inner_apply
        continuous_id (ξ i) (η i))
    · exact Complex.continuous_re.comp (ContinuousLinearMapWOT.continuous_inner_apply
        continuous_id (η i) (ξ i))
  have ha (a : H →L[ℂ] H) (ha : a ∈ A) : F (ContinuousLinearMapWOT.ofCLM a) = 0 := by
    have hh := horth (a + star a) (A.add_mem ha (A.star_mem' ha)) (IsSelfAdjoint.add_star_self _)
    have hsum : diagonalOp n (a + star a) ξ = diagonalOp n a ξ + star (diagonalOp n a) ξ := by
      rw [← diagonalOp_star]; ext i; rfl
    rw [hsum, inner_add_left, Complex.add_re] at hh
    simp only [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, Complex.re_sum] at hh
    simpa only [F, Finset.sum_add_distrib, diagonalOp_apply, ContinuousLinearMapWOT.ofCLM_apply] using hh
  have hF : F (ContinuousLinearMapWOT.ofCLM T) = 0 :=
    closure_minimal (by rintro _ ⟨a, ha', rfl⟩; exact ha a ha')
      (isClosed_eq hc continuous_const) hT
  have hsymm := congrArg Complex.re ((hsa.map (diagonalHom (H := H) n)).isSymmetric ξ η)
  change (inner ℂ (diagonalOp n T ξ) η).re = (inner ℂ ξ (diagonalOp n T η)).re at hsymm
  have hh : (inner ℂ (diagonalOp n T ξ) η).re +
      (inner ℂ ξ (diagonalOp n T η)).re = 0 := by
    simpa only [F, Finset.sum_add_distrib, PiLp.inner_apply, Complex.re_sum, diagonalOp_apply, ContinuousLinearMapWOT.ofCLM_apply] using hF
  linarith

lemma weakClosure_selfadjoint_strong_density
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ weakClosure A) (hsa : IsSelfAdjoint T)
    (n : ℕ) (ξ : Fin n → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, IsSelfAdjoint a ∧ ∀ i, ‖a (ξ i) - T (ξ i)‖ < ε := by
  let x : HilbertTuple n H := WithLp.toLp 2 ξ
  let : InnerProductSpace ℝ (HilbertTuple n H) := InnerProductSpace.rclikeToReal ℂ _
  let K := (nonunitalSelfAdjointOrbit A n x).range
  have hm : diagonalOp n T x ∈ K.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro η hη
    change (inner ℂ (diagonalOp n T x) η).re = 0
    apply weakClosure_selfadjoint_orthogonal A T hT hsa n x η
    intro a ha hsa_a
    let aA : A := ⟨a, ha⟩
    have haA : IsSelfAdjoint aA := by
      apply Subtype.ext
      exact hsa_a.star_eq
    let aS : selfAdjoint A := ⟨aA, haA⟩
    have hmem : nonunitalSelfAdjointOrbit A n x aS ∈ K := LinearMap.mem_range.mpr ⟨aS, rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hmem hη
  obtain ⟨y, hy, he⟩ := Metric.mem_closure_iff.mp hm ε hε
  obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hy
  refine ⟨a.val.val, a.val.property, congrArg Subtype.val a.property.star_eq, fun i => ?_⟩
  have hn : ‖diagonalOp n a.val.val x - diagonalOp n T x‖ < ε := by
    rw [dist_eq_norm] at he
    change ‖diagonalOp n T x - diagonalOp n a.val.val x‖ < ε at he
    rwa [norm_sub_rev] at he
  exact (PiLp.norm_apply_le (diagonalOp n a.val.val x - diagonalOp n T x) i).trans_lt hn

lemma nonunital_kaplansky_selfadjoint
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (hclosed : IsClosed (A : Set (H →L[ℂ] H)))
    (T : H →L[ℂ] H) (hT : T ∈ weakClosure A) (hsa : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1)
    (n : ℕ) (ξ : Fin n → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧ ∀ i, ‖a (ξ i) - T (ξ i)‖ < ε := by
  let b := cfc densityK T
  have hb : IsSelfAdjoint b := IsSelfAdjoint.cfc
  have hbmem : b ∈ weakClosure A := weakClosure_cfc A T hT densityK (by simp [densityK]) densityK_cont
  have hFb : densityf b = T := density_FK_operator T hsa hnorm
  obtain ⟨a, ha, hsa_a, he⟩ := weakClosure_selfadjoint_strong_density A b hbmem hb (n+n)
    (Fin.addCases (fun i => densityg b (ξ i)) (fun i => densityh b (ξ i)))
    (ε/4) (by positivity)
  have : IsClosed (A : Set (H →L[ℂ] H)) := hclosed
  have hmem : densityf a ∈ A := by
    unfold densityf
    rw [← cfcₙ_eq_cfc (f := densityF) (a := a) densityF_cont.continuousOn (by simp [densityF, densityH])]
    exact cfcₙ_mem (𝕜' := ℂ) densityF ha
  refine ⟨densityf a, hmem, density_selfadjoint a, densityf_norm a, fun i => ?_⟩
  have he₁ : ‖a (densityg b (ξ i)) - b (densityg b (ξ i))‖ < ε/4 := by
    simpa only [Fin.addCases_left] using he (Fin.castAdd n i)
  have he₂ : ‖a (densityh b (ξ i)) - b (densityh b (ξ i))‖ < ε/4 := by
    simpa only [Fin.addCases_right] using he (Fin.natAdd n i)
  rw [← hFb, densityf_eq, densityf_eq]
  simp only [smul_apply, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hh := densityh_apply_difference a b hsa_a hb (ξ i)
  linarith

def nonunitalMatrixSubalgebra (n : ℕ) (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    NonUnitalStarSubalgebra ℂ (HilbertTuple n H →L[ℂ] HilbertTuple n H) where
  carrier := {R | ∀ i j, matrixEntry n R i j ∈ A}
  zero_mem' := by intro i j; simp
  add_mem' hR hS := by intro i j; simpa using A.add_mem (hR i j) (hS i j)
  mul_mem' hR hS := by
    intro i j
    rw [matrixEntry_mul]
    exact A.sum_mem (fun k _ => A.mul_mem (hR i k) (hS k j))
  smul_mem' r R hR := by
    intro i j
    rw [matrixEntry_smul]
    exact A.smul_mem r (hR i j)
  star_mem' hR := by
    intro i j
    rw [matrixEntry_star]
    exact A.star_mem' (hR j i)

lemma nonunitalMatrixSubalgebra_closed (n : ℕ) (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsClosed (A : Set (H →L[ℂ] H))) : IsClosed (nonunitalMatrixSubalgebra n A : Set (HilbertTuple n H →L[ℂ] HilbertTuple n H)) := by
  change IsClosed {R | ∀ i j, matrixEntry n R i j ∈ A}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_iInter (fun j => hA.preimage (matrixEntry_continuous n i j)))

lemma diagonal_mem_nonunitalMatrixSubalgebra (n : ℕ) (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (a : H →L[ℂ] H) (ha : a ∈ A) : diagonalOp n a ∈ nonunitalMatrixSubalgebra n A := by
  intro i j
  rw [matrixEntry_diagonal]
  split_ifs <;> simp_all

lemma blockOp_mem_nonunitalMatrixSubalgebra (n : ℕ)
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (i j : Fin n)
    (T : H →L[ℂ] H) (hT : T ∈ A) : blockOp n i j T ∈ nonunitalMatrixSubalgebra n A := by
  intro k l
  rw [matrixEntry_blockOp]
  split_ifs <;> simp_all

lemma blockOp_WOT_continuous (n : ℕ) (i j : Fin n) :
    Continuous (fun a : H →WOT[ℂ] H => ContinuousLinearMapWOT.ofCLM (blockOp n i j a.toCLM)) := by
  apply ContinuousLinearMapWOT.continuous
  intro x y
  change Continuous (fun a : H →WOT[ℂ] H => inner ℂ y (tupleInclusion n i (a (x j))))
  simp_rw [tuple_inclusion_inner]
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id (x j) (y i)

lemma offDiagonal_WOT_continuous :
    Continuous (fun a : H →WOT[ℂ] H => ContinuousLinearMapWOT.ofCLM (offDiagonalOp a.toCLM)) := by
  change Continuous (fun a : H →WOT[ℂ] H =>
    ContinuousLinearMapWOT.ofCLM (blockOp 2 0 1 a.toCLM) +
      star (ContinuousLinearMapWOT.ofCLM (blockOp 2 0 1 a.toCLM)))
  exact (blockOp_WOT_continuous 2 0 1).add (blockOp_WOT_continuous 2 0 1).star

lemma offDiagonal_weakClosure (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ weakClosure A) :
    offDiagonalOp T ∈ weakClosure (nonunitalMatrixSubalgebra 2 A) := by
  apply map_mem_closure (offDiagonal_WOT_continuous (H := H)) hT
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨offDiagonalOp a, ?_, rfl⟩
  have hb := blockOp_mem_nonunitalMatrixSubalgebra 2 A 0 1 a ha
  exact (nonunitalMatrixSubalgebra 2 A).add_mem hb
    ((nonunitalMatrixSubalgebra 2 A).star_mem' hb)

/-- Literal norm-bounded strong-star density in the weak operator closure, valid
also for degenerate nonunital representations. -/
theorem nonunital_kaplansky_strong_star
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hclosed : IsClosed (A : Set (H →L[ℂ] H))) (T : H →L[ℂ] H)
    (hT : ContinuousLinearMapWOT.ofCLM T ∈ closure
      (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[ℂ] H))))
    (hnorm : ‖T‖ ≤ 1) (n : ℕ) (ξ : Fin n → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, ‖a‖ ≤ 1 ∧ ∀ i,
      ‖a (ξ i) - T (ξ i)‖ < ε ∧ ‖star a (ξ i) - star T (ξ i)‖ < ε := by
  obtain ⟨R, hR, hsa, hnormR, he⟩ := nonunital_kaplansky_selfadjoint
    (nonunitalMatrixSubalgebra 2 A) (nonunitalMatrixSubalgebra_closed 2 A hclosed) (offDiagonalOp T)
    (offDiagonal_weakClosure A T hT) (offDiagonal_selfadjoint T) (offDiagonal_norm T hnorm)
    (n+n) (Fin.addCases (fun i => tupleInclusion 2 1 (ξ i))
      (fun i => tupleInclusion 2 0 (ξ i))) ε hε
  refine ⟨matrixEntry 2 R 0 1, hR 0 1, (matrixEntry_norm 2 R 0 1).trans hnormR, fun i => ?_⟩
  have he₁ : ‖R (tupleInclusion 2 1 (ξ i)) - offDiagonalOp T (tupleInclusion 2 1 (ξ i))‖ < ε := by
    simpa only [Fin.addCases_left] using he (Fin.castAdd n i)
  have he₂ : ‖R (tupleInclusion 2 0 (ξ i)) - offDiagonalOp T (tupleInclusion 2 0 (ξ i))‖ < ε := by
    simpa only [Fin.addCases_right] using he (Fin.natAdd n i)
  constructor
  · have hh := (PiLp.norm_apply_le
      (R (tupleInclusion 2 1 (ξ i)) - offDiagonalOp T (tupleInclusion 2 1 (ξ i))) (0:Fin 2)).trans_lt he₁
    simpa [matrixEntry_apply] using hh
  · rw [← matrixEntry_star, hsa.star_eq]
    have hh := (PiLp.norm_apply_le
      (R (tupleInclusion 2 0 (ξ i)) - offDiagonalOp T (tupleInclusion 2 0 (ξ i))) (1:Fin 2)).trans_lt he₂
    simpa [matrixEntry_apply] using hh

omit [CompleteSpace H] in
lemma matrixEntry_decomposition (n : ℕ) (T : HilbertTuple n H →L[ℂ] HilbertTuple n H) :
    T = ∑ i, ∑ j, blockOp n i j (matrixEntry n T i j) := by
  ext x k
  have hd := congrArg (fun y => T y k) (tuple_decomposition n x)
  simpa [blockOp_apply, matrixEntry_apply] using hd

lemma matrix_weakClosure (n : ℕ) (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (T : HilbertTuple n H →L[ℂ] HilbertTuple n H)
    (hT : ∀ i j, matrixEntry n T i j ∈ weakClosure A) :
    T ∈ weakClosure (nonunitalMatrixSubalgebra n A) := by
  rw [matrixEntry_decomposition n T]
  apply (weakClosure (nonunitalMatrixSubalgebra n A)).sum_mem
  intro i _
  apply (weakClosure (nonunitalMatrixSubalgebra n A)).sum_mem
  intro j _
  apply map_mem_closure (blockOp_WOT_continuous n i j) (hT i j)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨_, blockOp_mem_nonunitalMatrixSubalgebra n A i j a ha, rfl⟩

/-- Matrix-level version for approximating positive Choi square roots; every
approximating entry remains in the fixed hereditary algebra. -/
theorem nonunital_matrix_kaplansky
    (m : ℕ) (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hclosed : IsClosed (A : Set (H →L[ℂ] H)))
    (T : HilbertTuple m H →L[ℂ] HilbertTuple m H)
    (hT : ∀ i j, matrixEntry m T i j ∈ weakClosure A) (hnorm : ‖T‖ ≤ 1)
    (n : ℕ) (ξ : Fin n → HilbertTuple m H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : HilbertTuple m H →L[ℂ] HilbertTuple m H,
      (∀ i j, matrixEntry m a i j ∈ A) ∧ ‖a‖ ≤ 1 ∧ ∀ i,
        ‖a (ξ i) - T (ξ i)‖ < ε ∧ ‖star a (ξ i) - star T (ξ i)‖ < ε :=
  nonunital_kaplansky_strong_star (nonunitalMatrixSubalgebra m A)
    (nonunitalMatrixSubalgebra_closed m A hclosed) T (matrix_weakClosure m A T hT) hnorm n ξ ε hε

end TraceConeClassification

namespace TraceConeClassification
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Strong-star approximation on finitely many vectors, without a norm bound on
the approximants. No closed-range assumption is necessary. -/
lemma weakClosure_strong_star_density (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ weakClosure A)
    (n : ℕ) (ξ : Fin n → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, ∀ i, ‖a (ξ i)-T (ξ i)‖ < ε ∧ ‖star a (ξ i)-star T (ξ i)‖ < ε := by
  obtain ⟨R,hR,hsa,he⟩ := weakClosure_selfadjoint_strong_density
    (nonunitalMatrixSubalgebra 2 A) (offDiagonalOp T)
    (offDiagonal_weakClosure A T hT) (offDiagonal_selfadjoint T)
    (n+n) (Fin.addCases (fun i => tupleInclusion 2 1 (ξ i))
      (fun i => tupleInclusion 2 0 (ξ i))) ε hε
  refine ⟨matrixEntry 2 R 0 1,hR 0 1,fun i => ?_⟩
  have he₁ : ‖R (tupleInclusion 2 1 (ξ i)) - offDiagonalOp T (tupleInclusion 2 1 (ξ i))‖ < ε := by
    simpa only [Fin.addCases_left] using he (Fin.castAdd n i)
  have he₂ : ‖R (tupleInclusion 2 0 (ξ i)) - offDiagonalOp T (tupleInclusion 2 0 (ξ i))‖ < ε := by
    simpa only [Fin.addCases_right] using he (Fin.natAdd n i)
  constructor
  · have hh := (PiLp.norm_apply_le
      (R (tupleInclusion 2 1 (ξ i))-offDiagonalOp T (tupleInclusion 2 1 (ξ i))) (0:Fin 2)).trans_lt he₁
    simpa [matrixEntry_apply] using hh
  · rw [← matrixEntry_star,hsa.star_eq]
    have hh := (PiLp.norm_apply_le
      (R (tupleInclusion 2 0 (ξ i))-offDiagonalOp T (tupleInclusion 2 0 (ξ i))) (1:Fin 2)).trans_lt he₂
    simpa [matrixEntry_apply] using hh

end TraceConeClassification

end

end OAI
