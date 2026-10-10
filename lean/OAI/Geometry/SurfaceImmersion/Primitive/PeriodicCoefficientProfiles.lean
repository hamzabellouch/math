import OAI.Geometry.SurfaceImmersion.Geometry.CompactAnsatzAsymptotics
import OAI.Geometry.SurfaceImmersion.Primitive.LocalAnsatzProfiles

namespace OAI

/-! Explicit finite coefficient bounds for the varying-map version of the
periodic derivative estimates. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.PeriodicExpansion
open CovarianceCorrector
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma phaseSum_bound_of_coefficients (U : ℕ → Family A E)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) {z C : ℝ} {p : A}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hU : ∀ i < L, ‖(U i).fastValue ℓ z p‖ ≤ C) :
    ‖phaseSum U ℓ L z p‖ ≤ L*C := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ i ∈ Finset.range L, ‖z^i • (U i).fastValue ℓ z p‖ ≤
        ∑ _i ∈ Finset.range L, C := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hz _)]
      exact (mul_le_mul_of_nonneg_left (hU i (Finset.mem_range.mp hi)) (pow_nonneg hz _)).trans
        (mul_le_of_le_one_left hC (pow_le_one₀ hz hz1))
    _ = L*C := by simp

lemma phaseSum_tail_bound_of_coefficients (U : ℕ → Family A E)
    (ℓ : A →L[ℝ] ℝ) (n : ℕ) {z C : ℝ} {p : A}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hU : ∀ i < n+1, ‖(U i).fastValue ℓ z p‖ ≤ C) :
    ‖phaseSum U ℓ (n+1) z p-(U 0).fastValue ℓ z p‖ ≤ (n*C)*z := by
  rw [phaseSum_leading,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hz]
  have hh := phaseSum_bound_of_coefficients (fun i => U (i+1)) ℓ n hz hz1 hC
    (fun i hi => hU (i+1) (by omega))
  exact (mul_le_mul_of_nonneg_left hh hz).trans_eq (mul_comm _ _)

/-- The two transverse derivatives only differentiate slow coefficients. -/
theorem transverse_profiles_of_coefficients {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (L : ℕ) {dy : A} (hy : ℓ dy = 0)
    {z C : ℝ} {p : A} (hz : 0 < z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hU : ∀ i < L, ‖((U i).slow dy).fastValue ℓ z p‖ ≤ C)
    (hUU : ∀ i < L, ‖(((U i).slow dy).slow dy).fastValue ℓ z p‖ ≤ C) :
    ‖directionalMap (finiteAnsatz F U ℓ L z) dy p-directionalMap F dy p‖ ≤ (L*C)*z ∧
    ‖directionalMap (directionalMap (finiteAnsatz F U ℓ L z) dy) dy p-
      directionalMap (directionalMap F dy) dy p‖ ≤ (L*C)*z := by
  constructor
  · rw [finiteAnsatz_directional hF U ℓ L hz.ne' dy]
    simp only [hy,zero_smul,add_zero,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hz]
    exact (mul_le_mul_of_nonneg_left (phaseSum_bound_of_coefficients _ ℓ L hz.le hz1 hC hU) hz.le).trans_eq
      (mul_comm _ _)
  · rw [finiteAnsatz_second_transverse hF U ℓ L hz.ne' dy hy]
    simp only [hy,zero_smul,add_zero,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hz]
    exact (mul_le_mul_of_nonneg_left (phaseSum_bound_of_coefficients _ ℓ L hz.le hz1 hC hUU) hz.le).trans_eq
      (mul_comm _ _)

end ClosedSurfaceR4.PeriodicExpansion

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

lemma global_slow_eq_local (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : W.val = U.val) (v : A) {p : A} (hp : p ∈ O) (t : Period) :
    (W.slow v).val p t = (U.slow v).val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.slow_apply,Family.slow_apply U v hp,hW]

lemma global_slow_eq_local_of_eqOn (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : ∀ p ∈ O, ∀ t : Period, W.val p t = U.val p t)
    (v : A) {p : A} (hp : p ∈ O) (t : Period) :
    (W.slow v).val p t = (U.slow v).val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.slow_apply,Family.slow_apply U v hp]
  have he : (fun z : A × ℝ => W.val z.1 (z.2 : Period)) =ᶠ[nhds (p,s)]
      (fun z => U.val z.1 (z.2 : Period)) := by
    filter_upwards [(O.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ s⟩] with z hz
    exact hW z.1 hz.1 (z.2 : Period)
  exact congrArg (fun L : (A × ℝ) →L[ℝ] E => L (v,0)) he.fderiv_eq

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
