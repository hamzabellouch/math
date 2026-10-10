import OAI.Geometry.SurfaceImmersion.Geometry.SafeRadialNormalization
import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingAtlas

namespace OAI

/-! The fixed smooth extension acts uniformly continuously on bounded
first jets. This gives the C1 stability used in finite-point preparation. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets
open WeightedEstimates
abbrev SafeFirstJet := Space × (JetPolynomial.Base →L[ℝ] Space)

def safeNormalizeFirstJet (J : SafeFirstJet) : SafeFirstJet :=
  (safeRadialNormalize J.1,(fderiv ℝ safeRadialNormalize J.1).comp J.2)

lemma safeNormalizeFirstJet_continuous : Continuous safeNormalizeFirstJet := by
  exact (safeRadialNormalize_smooth.continuous.comp continuous_fst).prodMk
    (((safeRadialNormalize_smooth.fderiv_right (m := ∞) (by simp)).continuous.comp
      continuous_fst).clm_comp continuous_snd)

theorem safe_normalization_first_jet_stability (C : ℝ) (_hC : 0 ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (x y : Space) (L A : JetPolynomial.Base →L[ℝ] Space),
      ‖x‖ ≤ C → ‖L‖ ≤ C → ‖y-x‖ ≤ δ → ‖A-L‖ ≤ δ →
      ‖safeRadialNormalize y-safeRadialNormalize x‖ ≤ ε ∧
        ‖(fderiv ℝ safeRadialNormalize y).comp A-
          (fderiv ℝ safeRadialNormalize x).comp L‖ ≤ ε := by
  have hu := (isCompact_closedBall (0 : SafeFirstJet) (C+1)).uniformContinuousOn_of_continuous
    safeNormalizeFirstJet_continuous.continuousOn
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min 1 (d/2),lt_min zero_lt_one (half_pos hd),min_le_left _ _,?_⟩
  intro x y L A hx hL hy hA
  let J : SafeFirstJet := (x,L)
  let H : SafeFirstJet := (y,A)
  have hJ : ‖J‖ ≤ C := max_le hx hL
  have hHJ : ‖H-J‖ ≤ min 1 (d/2) := max_le hy hA
  have hH : ‖H‖ ≤ C+1 := by
    calc
      ‖H‖ ≤ ‖H-J‖+‖J‖ := norm_le_norm_sub_add H J
      _ ≤ C+1 := by linarith [min_le_left (1 : ℝ) (d/2)]
  have hdist : dist H J < d := by
    rw [dist_eq_norm]
    exact hHJ.trans_lt ((min_le_right (1 : ℝ) (d/2)).trans_lt (half_lt_self hd))
  have hh := hclose H (by simpa only [mem_closedBall,dist_zero_right] using hH)
    J (by simpa only [mem_closedBall,dist_zero_right] using hJ.trans (by linarith : C ≤ C+1)) hdist
  rw [dist_eq_norm] at hh
  exact ⟨(norm_fst_le _).trans hh.le,(norm_snd_le _).trans hh.le⟩

theorem safe_normalization_C1_stability (f : JetPolynomial.Base → Space)
    (hf : ContDiff ℝ ∞ f) (C : ℝ) (hC : 0 ≤ C)
    (hb : WeightedBound univ 1 1 C f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : JetPolynomial.Base → Space,
      ContDiff ℝ ∞ q → WeightedBound univ 1 1 δ q →
      WeightedBound univ 1 1 ε (fun x => safeRadialNormalize (f x+q x)-safeRadialNormalize (f x)) := by
  obtain ⟨δ,hδ,_,hd⟩ := safe_normalization_first_jet_stability C hC hε
  refine ⟨δ,hδ,?_⟩
  intro q hq hqb
  have hpoint (x : JetPolynomial.Base) :
      ‖safeRadialNormalize (f x+q x)-safeRadialNormalize (f x)‖ ≤ ε ∧
      ‖fderiv ℝ (fun x => safeRadialNormalize (f x+q x)-safeRadialNormalize (f x)) x‖ ≤ ε := by
    have hf₁ := hb 1 le_rfl x (mem_univ x)
    have hq₁ := hqb 1 le_rfl x (mem_univ x)
    simp only [one_pow,one_mul,iteratedFDerivWithin_univ,norm_iteratedFDeriv_one] at hf₁ hq₁
    have hh := hd (f x) (f x+q x) (fderiv ℝ f x) (fderiv ℝ (f+q) x)
      (hb.norm_le (mem_univ x)) hf₁ (by simpa using hqb.norm_le (mem_univ x)) (by
        rw [fderiv_add (hf.differentiable (by simp) x) (hq.differentiable (by simp) x)]
        simpa using hq₁)
    refine ⟨hh.1,?_⟩
    have hs : HasFDerivAt (fun y => f y+q y) (fderiv ℝ f x+fderiv ℝ q x) x :=
      (hf.differentiable (by simp) x).hasFDerivAt.add
        (hq.differentiable (by simp) x).hasFDerivAt
    have hg := ((safeRadialNormalize_smooth.differentiable (by simp) (f x+q x)).hasFDerivAt.comp x hs).sub
      ((safeRadialNormalize_smooth.differentiable (by simp) (f x)).hasFDerivAt.comp x
        (hf.differentiable (by simp) x).hasFDerivAt)
    have hdf : fderiv ℝ (fun y => safeRadialNormalize (f y+q y)-safeRadialNormalize (f y)) x =
        (fderiv ℝ safeRadialNormalize (f x+q x)).comp (fderiv ℝ f x+fderiv ℝ q x)-
          (fderiv ℝ safeRadialNormalize (f x)).comp (fderiv ℝ f x) := hg.fderiv
    rw [hdf]
    have hs' : fderiv ℝ (f+q) x = fderiv ℝ f x+fderiv ℝ q x := hs.fderiv
    rw [hs'] at hh
    exact hh.2
  intro j hj x hx
  interval_cases j
  · simpa using (hpoint x).1
  · simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,norm_iteratedFDeriv_one] using (hpoint x).2

end ClosedSurfaceR4.SphericalJets

end

end OAI
