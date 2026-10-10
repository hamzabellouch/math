import OAI.Combinatorics.SparsestCut.PivotFamily

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartLinear
variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F]

lemma gram_injective (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) : Function.Injective (J.adjoint.comp J) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hh : ‖J x‖^2 = 0 := by
    have := congrArg (fun z => inner ℝ x z) hx
    change inner ℝ x (J.adjoint (J x)) = inner ℝ x 0 at this
    simpa only [J.adjoint_inner_right, real_inner_self_eq_norm_sq, inner_zero_right] using this
  have hn : ‖x‖^2 = 0 := by nlinarith [hl x, sq_nonneg ‖x‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

noncomputable def gramEquiv (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective (J.adjoint.comp J)
    (LinearMap.ker_eq_bot.mpr (gram_injective J ha hl))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp
      (gram_injective J ha hl)))

noncomputable def pseudoInverse (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) : F →L[ℝ] E :=
  (gramEquiv J ha hl).symm.toContinuousLinearMap.comp J.adjoint

lemma pseudoInverse_comp (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) : (pseudoInverse J ha hl).comp J = ContinuousLinearMap.id ℝ E := by
  ext x
  exact (gramEquiv J ha hl).symm_apply_apply x

lemma gramInverse_norm (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : E) :
    ‖(gramEquiv J ha hl).symm y‖ ≤ ‖y‖/a := by
  let x := (gramEquiv J ha hl).symm y
  have hx : J.adjoint (J x) = y := (gramEquiv J ha hl).apply_symm_apply y
  have hb := hl x
  have he : ‖J x‖^2 = inner ℝ x y := by rw [← hx, J.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [he] at hb
  have hc := real_inner_le_norm x y
  by_cases hz : ‖x‖ = 0
  · simpa [x, hz] using (div_nonneg (norm_nonneg y) ha.le)
  · have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖x‖ ≤ ‖y‖/a
    apply (le_div_iff₀ ha).mpr
    nlinarith

lemma pseudoInverse_equation (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) :
    J.adjoint (J (pseudoInverse J ha hl y)) = J.adjoint y :=
  (gramEquiv J ha hl).apply_symm_apply _

lemma residual_orthogonal (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) (x : E) :
    inner ℝ (J x) (y - J (pseudoInverse J ha hl y)) = 0 := by
  rw [← J.adjoint_inner_right]
  simp [pseudoInverse_equation J ha hl y]

lemma residual_pythagoras (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) :
    ‖J (pseudoInverse J ha hl y)‖^2 + ‖y-J (pseudoInverse J ha hl y)‖^2 = ‖y‖^2 := by
  have h := norm_add_sq_real (J (pseudoInverse J ha hl y)) (y - J (pseudoInverse J ha hl y))
  rw [residual_orthogonal] at h
  simpa using h.symm

lemma pseudoInverse_norm (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) :
    ‖pseudoInverse J ha hl y‖ ≤ ‖y‖ / Real.sqrt a := by
  have hr := residual_pythagoras J ha hl y
  have hb := hl (pseudoInverse J ha hl y)
  have hs := Real.sq_sqrt ha.le
  apply (le_div_iff₀ (Real.sqrt_pos.2 ha)).mpr
  nlinarith [sq_nonneg ‖y-J (pseudoInverse J ha hl y)‖,
    norm_nonneg (pseudoInverse J ha hl y), norm_nonneg y, Real.sqrt_nonneg a]

lemma residual_norm (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) :
    ‖y-J (pseudoInverse J ha hl y)‖ ≤ ‖y‖ := by
  have h := residual_pythagoras J ha hl y
  nlinarith [norm_nonneg y, norm_nonneg (y-J (pseudoInverse J ha hl y)),
    sq_nonneg ‖J (pseudoInverse J ha hl y)‖]

lemma pseudoInverse_column (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) :
    ‖pseudoInverse J ha hl y‖ ≤ ‖J.adjoint y‖/a :=
  gramInverse_norm J ha hl _

end UniformSparsestCut.ChartLinear

namespace UniformSparsestCut.FrameCharts
open scoped RealInnerProductSpace BigOperators
variable {m N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)

def chart (u : Fin N → E) : E →L[ℝ] F :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (u i)))

@[simp] lemma chart_apply (u : Fin N → E) (x : E) (i : Fin N) :
    chart u x i = inner ℝ (u i) x := rfl

lemma chart_energy (u : Fin N → E) (x : E) :
    ‖chart u x‖^2 = ∑ i, (inner ℝ (u i) x)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [chart_apply, Real.norm_eq_abs, sq_abs]

lemma chart_adjoint_single (u : Fin N → E) (i : Fin N) :
    (chart u).adjoint (EuclideanSpace.single i 1) = u i := by
  apply ext_inner_right ℝ
  intro x
  rw [(chart u).adjoint_inner_left]
  change inner ℝ (EuclideanSpace.single i 1) (chart u x) = inner ℝ (u i) x
  rw [EuclideanSpace.inner_single_left]
  simp

lemma extend_covariance (g : Fin N → E) (hN : 0 < N) (a b : ℝ)
    (hc : ∀ v : E, ‖v‖ = 1 → a ≤ (∑ i, (inner ℝ v (g i))^2)/(N : ℝ) ∧
      (∑ i, (inner ℝ v (g i))^2)/(N : ℝ) ≤ b) (x : E) :
    a*(N : ℝ)*‖x‖^2 ≤ ∑ i, (inner ℝ (g i) x)^2 ∧
      (∑ i, (inner ℝ (g i) x)^2) ≤ b*(N : ℝ)*‖x‖^2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hx : x = 0
  · simp [hx]
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let v : E := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hx0.ne']
  have he : (∑ i, (inner ℝ v (g i))^2) = ‖x‖⁻¹^2 * ∑ i, (inner ℝ (g i) x)^2 := by
    simp only [v, real_inner_smul_left, mul_pow, Finset.mul_sum]
    congr 1
    funext i
    rw [real_inner_comm]
  obtain ⟨hl,hu⟩ := hc v hv
  rw [div_le_iff₀ hn] at hu
  rw [le_div_iff₀ hn] at hl
  rw [he] at hl hu
  have hsq : 0 ≤ ‖x‖^2 := sq_nonneg _
  constructor
  · have h := mul_le_mul_of_nonneg_right hl hsq
    have hz : ‖x‖⁻¹^2*‖x‖^2 = 1 := by field_simp
    calc
      _ ≤ _ := h
      _ = _ := by rw [mul_right_comm, hz, one_mul]
  · have h := mul_le_mul_of_nonneg_right hu hsq
    have hz : ‖x‖⁻¹^2*‖x‖^2 = 1 := by field_simp
    calc
      _ = _ := by rw [mul_right_comm, hz, one_mul]
      _ ≤ _ := h

lemma normalized_energy (g : Fin N → E) (_hm : 0 < m) (x : E) :
    ‖chart (fun i => (Real.sqrt m)⁻¹ • g i) x‖^2 =
      (∑ i, (inner ℝ (g i) x)^2)/(m : ℝ) := by
  rw [chart_energy]
  simp only [real_inner_smul_left, mul_pow, ← Finset.mul_sum]
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg m), div_eq_inv_mul]

lemma normalized_bounds (g : Fin N → E) (hm : 0 < m) (hN : 0 < N)
    (hc : ∀ v : E, ‖v‖ = 1 → 1/2 ≤ (∑ i, (inner ℝ v (g i))^2)/(N : ℝ) ∧
      (∑ i, (inner ℝ v (g i))^2)/(N : ℝ) ≤ 2) (x : E) :
    ((N : ℝ)/(2*m))*‖x‖^2 ≤ ‖chart (fun i => (Real.sqrt m)⁻¹ • g i) x‖^2 ∧
    ‖chart (fun i => (Real.sqrt m)⁻¹ • g i) x‖^2 ≤ ((2*N : ℝ)/m)*‖x‖^2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hl,hu⟩ := extend_covariance g hN (1/2) 2 hc x
  rw [normalized_energy g hm x]
  constructor
  · apply (le_div_iff₀ hm0).mpr
    calc
      _ = (1/2:ℝ)*N*‖x‖^2 := by field_simp
      _ ≤ _ := hl
  · apply (div_le_iff₀ hm0).mpr
    calc
      _ ≤ (2:ℝ)*N*‖x‖^2 := hu
      _ = _ := by field_simp

lemma normalized_norms (g : Fin N → E) (hm : 0 < m)
    (hg : ∀ i, Real.sqrt m/2 ≤ ‖g i‖ ∧ ‖g i‖ ≤ 2*Real.sqrt m) (i : Fin N) :
    1/2 ≤ ‖(Real.sqrt m)⁻¹ • g i‖ ∧ ‖(Real.sqrt m)⁻¹ • g i‖ ≤ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), ← div_eq_inv_mul]
  constructor
  · exact (le_div_iff₀ hs).mpr (by linarith [(hg i).1])
  · exact (div_le_iff₀ hs).mpr (hg i).2

end UniformSparsestCut.FrameCharts

end

end OAI
