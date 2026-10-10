import OAI.Geometry.NodalSets.Elliptic.CorrugationAffineJets
import OAI.Geometry.NodalSets.Elliptic.CorrugationCutoff
import OAI.Geometry.NodalSets.Elliptic.CorrugationRadialJetsLemmas

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

def corrugationSlowMap (R : ℝ) : Coord →L[ℝ] Coord :=
  R⁻¹ • ContinuousLinearMap.id ℝ Coord

def corrugationFastMap (J : ℝ) (a b : Coord →L[ℝ] ℝ) : Coord →L[ℝ] (ℝ × ℝ) :=
  J • a.prod b

def localizedCorrugation (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (s J R : ℝ) (a b : Coord →L[ℝ] ℝ) (y x : Coord) : ℝ :=
  (s/J)*χ (corrugationSlowMap R (x-y))*f (corrugationFastMap J a b (x-y))

lemma localizedCorrugation_formula (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (s J R : ℝ) (a b : Coord →L[ℝ] ℝ) (y x : Coord) :
    localizedCorrugation χ f s J R a b y x =
      (s/J)*χ (R⁻¹ • (x-y))*f (J*a (x-y),J*b (x-y)) := rfl

lemma localizedCorrugation_smooth (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s J R : ℝ) (a b : Coord →L[ℝ] ℝ) (y : Coord) :
    ContDiff ℝ ∞ (localizedCorrugation χ f s J R a b y) :=
  (contDiff_const.mul (hχ.comp ((corrugationSlowMap R).contDiff.comp
    (contDiff_id.sub contDiff_const)))).mul
    (hf.comp ((corrugationFastMap J a b).contDiff.comp (contDiff_id.sub contDiff_const)))

lemma localizedCorrugation_support (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (s J : ℝ) {R : ℝ} (a b : Coord →L[ℝ] ℝ) (y : Coord) :
    tsupport (localizedCorrugation χ f s J R a b y) ⊆
      (fun x ↦ R⁻¹ • (x-y)) ⁻¹' tsupport χ := by
  apply closure_minimal
  · intro x hx
    apply subset_tsupport
    intro hz
    exact hx (by simp [localizedCorrugation,corrugationSlowMap,hz])
  · exact (isClosed_closure : IsClosed (tsupport χ)).preimage ((continuous_const : Continuous (fun _ : Coord ↦ R⁻¹)).smul (continuous_id.sub continuous_const))

lemma localizedCorrugation_cube (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : tsupport χ ⊆ ball (0:Coord) (1/2))
    (s J : ℝ) {R : ℝ} (hR : 0 < R) (a b : Coord →L[ℝ] ℝ) (y : Coord) :
    tsupport (localizedCorrugation χ f s J R a b y) ⊆ ball y (R/2) := by
  intro x hx
  have hz := hχ (localizedCorrugation_support χ f s J a b y hx)
  rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)] at hz
  rw [mem_ball,dist_eq_norm]
  have hr : R*R⁻¹ = 1 := mul_inv_cancel₀ hR.ne'
  nlinarith [mul_lt_mul_of_pos_left hz hR]

lemma localizedCorrugation_compact (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : tsupport χ ⊆ ball (0:Coord) (1/2))
    (s J : ℝ) {R : ℝ} (hR : 0 < R) (a b : Coord →L[ℝ] ℝ) (y : Coord) :
    HasCompactSupport (localizedCorrugation χ f s J R a b y) :=
  (isCompact_closedBall y (R/2)).of_isClosed_subset isClosed_closure
    ((localizedCorrugation_cube χ f hχ s J hR a b y).trans ball_subset_closedBall)

lemma localizedCorrugation_collar (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : tsupport χ ⊆ ball (0:Coord) (1/2))
    (s J : ℝ) {R : ℝ} (hR : 0 < R) (a b : Coord →L[ℝ] ℝ) (y x : Coord)
    (hx : x ∉ ball y (R/2)) :
    localizedCorrugation χ f s J R a b y =ᶠ[𝓝 x] 0 := by
  exact notMem_tsupport_iff_eventuallyEq.mp
    (fun h ↦ hx (localizedCorrugation_cube χ f hχ s J hR a b y h))

lemma localizedCorrugation_bound (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ∀ z, |χ z| ≤ 1) {B : ℝ} (hf : ∀ z, |f z| ≤ B)
    {s J : ℝ} (hs : 0 ≤ s) (hJ : 0 < J) (R : ℝ)
    (a b : Coord →L[ℝ] ℝ) (y x : Coord) :
    |localizedCorrugation χ f s J R a b y x| ≤ (s/J)*B := by
  have hn : 0 ≤ s/J := div_nonneg hs hJ.le
  rw [localizedCorrugation,abs_mul,abs_mul,abs_of_nonneg hn]
  calc
    s/J*|χ _| *|f _| ≤ s/J*1*|f _| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hχ _) hn) (abs_nonneg _)
    _ ≤ (s/J)*B := by simpa using mul_le_mul_of_nonneg_left (hf _) hn

end
end Yau.Geometry

end OAI
