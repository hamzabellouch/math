import OAI.Geometry.NodalSets.Elliptic.CorrugationFirstAxis
import OAI.Geometry.NodalSets.Elliptic.CorrugationLeadingVector
import OAI.Geometry.NodalSets.Elliptic.CorrugationOldData

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma corrugationLeadingVector_pair
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (y : Coord) (hp : ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : metricGradient g S y ≠ 0) (e : Coord ≃L[ℝ] Coord)
    (he0 : e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y)
    (he : ∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) (v : Coord) :
    g y (corrugationOldSlope g S y • corrugationLeadingVector amp t e z) v =
      fderiv ℝ S y v + corrugationOldSlope g S y*t*
        fderiv ℝ (corrugationPeriodicWell amp) z
          ((frozenFrameCovector e 2).prod (frozenFrameCovector e 3) v) := by
  have hs := corrugationOldSlope_positive g S y hp hn
  simp only [corrugationLeadingVector,map_smul,map_add,smul_apply,
    add_apply,smul_eq_mul]
  rw [he0,map_smul,smul_apply,smul_eq_mul,
    metricGradient_pair g S y hp,corrugationFastVector_pair (g y) e he]
  field_simp

lemma corrugation_cutoff_residual_bound (χ : Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (amp : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s J R : ℝ), 0 ≤ s → 0 < J → 0 < R →
      ∀ (a b : Coord →L[ℝ] ℝ) (y x v : Coord),
      |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v -
        s*χ (R⁻¹ • (x-y))*fderiv ℝ (corrugationPeriodicWell amp)
          (corrugationFastMap J a b (x-y)) (a.prod b v)| ≤ s/(J*R)*C*‖v‖ := by
  obtain ⟨B,hB,hf⟩ := corrugationPeriodicWell_bounded amp
  obtain ⟨M,hM,hd⟩ := compact_first_derivative_bound χ hχ hc
  refine ⟨B*M,mul_pos hB hM,?_⟩
  intro s J R hs hJ hR a b y x v
  rw [localizedCorrugation_first_scaled χ _ hχ (corrugationPeriodicWell_smooth amp) s hJ.ne']
  rw [add_sub_cancel_left,abs_mul,abs_mul,abs_of_nonneg (div_nonneg hs (mul_pos hJ hR).le)]
  have hder : |fderiv ℝ χ (R⁻¹ • (x-y)) v| ≤ M*‖v‖ :=
    ((fderiv ℝ χ _).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hd _) (norm_nonneg v))
  calc
    _ ≤ (s/(J*R)*B)*(M*‖v‖) := mul_le_mul
      (mul_le_mul_of_nonneg_left (hf _) (by positivity)) hder (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem corrugation_frozen_differential_bound
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (amp : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J R A : ℝ), 0 < J → 0 < R → 0 ≤ A →
      ∀ (y x : Coord), (∀ v, v ≠ 0 → 0 < g y v v) →
      metricGradient g S y ≠ 0 → DifferentiableAt ℝ S x → ‖x-y‖ ≤ R →
      (∀ v, |fderiv ℝ S x v-fderiv ℝ S y v| ≤ A*‖x-y‖*‖v‖) →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ∀ v, |fderiv ℝ (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) J R (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x v -
        g y (corrugationOldSlope g S y • corrugationLeadingVector amp (χ (R⁻¹ • (x-y))) e
          (corrugationFastMap J (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))) v| ≤
        (A*R+corrugationOldSlope g S y/(J*R)*C)*‖v‖ := by
  obtain ⟨C,hC,hres⟩ := corrugation_cutoff_residual_bound χ hχ hc amp
  refine ⟨C,hC,?_⟩
  intro J R A hJ hR hA y x hp hn hS hxy hfreeze e he0 he v
  have hs := corrugationOldSlope_positive g S y hp hn
  have hw := (localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp)
    (corrugationOldSlope g S y) J R (frozenFrameCovector e 2) (frozenFrameCovector e 3) y).differentiable (by simp)
  rw [fderiv_add hS hw.differentiableAt,add_apply,
    corrugationLeadingVector_pair g S y hp hn e he0 he]
  have hr := hres (corrugationOldSlope g S y) J R hs.le hJ hR
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y x v
  calc
    _ ≤ |fderiv ℝ S x v-fderiv ℝ S y v|+
        |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp)
          (corrugationOldSlope g S y) J R (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x v -
          corrugationOldSlope g S y*χ (R⁻¹ • (x-y))*fderiv ℝ (corrugationPeriodicWell amp)
            (corrugationFastMap J (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
            ((frozenFrameCovector e 2).prod (frozenFrameCovector e 3) v)| := by
      convert abs_add_le (fderiv ℝ S x v-fderiv ℝ S y v) _ using 1
      congr 1
      ring
    _ ≤ A*R*‖v‖+corrugationOldSlope g S y/(J*R)*C*‖v‖ :=
      add_le_add ((hfreeze v).trans (by gcongr)) hr
    _ = _ := by ring

end
end Yau.Geometry

end OAI
