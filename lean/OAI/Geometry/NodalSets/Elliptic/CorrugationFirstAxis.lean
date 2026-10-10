import OAI.Geometry.NodalSets.Charts.CorrugationMetricError
import OAI.Geometry.NodalSets.Elliptic.CorrugationPeriodicBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma compact_first_derivative_bound (χ : Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ χ x‖ ≤ C := by
  have hcD : IsCompact (tsupport (fderiv ℝ χ)) :=
    hc.of_isClosed_subset isClosed_closure (tsupport_fderiv_subset ℝ (f := χ))
  have hcont : Continuous (fun x ↦ ‖fderiv ℝ χ x‖) := (hχ.continuous_fderiv (by simp)).norm
  obtain ⟨B,hB⟩ := (hcD.image hcont).bddAbove
  refine ⟨max B 0+1,by positivity,fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport (fderiv ℝ χ)
  · exact (hB ⟨x,hx,rfl⟩).trans (by linarith [le_max_left B 0])
  · have hz : fderiv ℝ χ x = 0 := by
      by_contra hn
      exact hx (subset_tsupport _ hn)
    rw [hz]
    simp only [ContinuousLinearMap.opNorm_zero]
    positivity

theorem corrugation_first_axis_bound (χ : Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (amp : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s J R : ℝ), 0 ≤ s → 0 < J → 0 < R →
      ∀ (a b : Coord →L[ℝ] ℝ) (y x v : Coord), a v = 0 → b v = 0 →
      |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v| ≤
        s/(J*R)*C*‖v‖ := by
  obtain ⟨B,hB,hf⟩ := corrugationPeriodicWell_bounded amp
  obtain ⟨M,hM,hd⟩ := compact_first_derivative_bound χ hχ hc
  refine ⟨B*M,mul_pos hB hM,?_⟩
  intro s J R hs hJ hR a b y x v ha hb
  rw [localizedCorrugation_first_scaled χ _ hχ (corrugationPeriodicWell_smooth amp) s hJ.ne']
  have hz : a.prod b v = 0 := by ext <;> assumption
  rw [hz,map_zero,mul_zero,zero_add,abs_mul,abs_mul,abs_of_nonneg (div_nonneg hs (mul_pos hJ hR).le)]
  have hder : |fderiv ℝ χ (R⁻¹ • (x-y)) v| ≤ M*‖v‖ :=
    ((fderiv ℝ χ _).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hd _) (norm_nonneg v))
  calc
    _ ≤ (s/(J*R)*B)*(M*‖v‖) := mul_le_mul
      (mul_le_mul_of_nonneg_left (hf _) (by positivity)) hder (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma corrugated_first_axis_positive (S : Coord → ℝ) (χ : Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (amp : ℝ)
    (s J R C A K : ℝ) (_hs : 0 < s) (hA : 0 ≤ A) (_hK : 0 ≤ K)
    (a b : Coord →L[ℝ] ℝ) (y x v : Coord)
    (hS : DifferentiableAt ℝ S x)
    (haxis : fderiv ℝ S y v = s)
    (hfreeze : |fderiv ℝ S x v-fderiv ℝ S y v| ≤ A*‖x-y‖*‖v‖)
    (hxy : ‖x-y‖ ≤ R) (hv : ‖v‖ ≤ K)
    (herr : |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v| ≤
      s/(J*R)*C*‖v‖)
    (hcoef : 0 ≤ s/(J*R)*C)
    (hsmall₁ : A*R*K ≤ s/4) (hsmall₂ : s/(J*R)*C*K ≤ s/4) :
    s/2 ≤ fderiv ℝ (fun z ↦ S z+localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y z) x v := by
  have hw := (localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp) s J R a b y).differentiable (by simp)
  change s/2 ≤ fderiv ℝ (S+localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v
  rw [fderiv_add hS hw.differentiableAt,add_apply]
  have hR : 0 ≤ R := (norm_nonneg (x-y)).trans hxy
  have hfreeze' : |fderiv ℝ S x v-s| ≤ s/4 := by
    rw [haxis] at hfreeze
    apply hfreeze.trans
    calc
      A*‖x-y‖*‖v‖ ≤ A*R*K := mul_le_mul (mul_le_mul_of_nonneg_left hxy hA) hv (norm_nonneg _) (by positivity)
      _ ≤ _ := hsmall₁
  have herr' : |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v| ≤ s/4 :=
    herr.trans ((mul_le_mul_of_nonneg_left hv hcoef).trans hsmall₂)
  have h1 := (abs_le.mp hfreeze').1
  have h2 := (abs_le.mp herr').1
  linarith

end
end Yau.Geometry

end OAI
