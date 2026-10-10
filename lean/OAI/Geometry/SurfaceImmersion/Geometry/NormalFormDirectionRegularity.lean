import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapComposedDirection

namespace OAI

/-! Smooth source and target coordinates preserve the nondegenerate
derivative-direction zero of an actual standard crosscap. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma axisDirectionJet_congr_germ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : Base → V} {p : Base} (h : f =ᶠ[𝓝 p] g) :
    axisDirectionJet f p = axisDirectionJet g p := by
  simp only [axisDirectionJet,h.fderiv_eq,h.fderiv.fderiv_eq]

lemma normal_form_direction_regularity {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) {g : Base → Base} (hg : ContDiff ℝ ∞ g)
    {H : Base × ℝ → ProjectionTarget 3} (hH : ContDiff ℝ ∞ H) (p : Base)
    (hp : g p = 0) (hgD : Function.Bijective (fderiv ℝ g p))
    (hHD : Function.Bijective (fderiv ℝ H 0))
    (hEq : φ =ᶠ[𝓝 p] H ∘ (standardCrosscap ∘ g))
    (hv : fderiv ℝ φ p (![0,1] : Base) = 0) :
    Function.Bijective (fderiv ℝ (surfaceDirection φ true) (p,0)) := by
  let G := standardCrosscap ∘ g
  have hG : ContDiff ℝ ∞ G := standardCrosscap_smooth.comp hg
  have hstd0 : standardCrosscap (0:Base) = 0 := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [standardCrosscap]
    · simp [standardCrosscap]
  have hGp : G p = 0 := by change standardCrosscap (g p) = 0; rw [hp,hstd0]
  have hfirst : fderiv ℝ φ p (![0,1] : Base) = fderiv ℝ H 0
      (standardCrosscapDerivative 0 (fderiv ℝ g p (![0,1] : Base))) := by
    rw [hEq.fderiv_eq,fderiv_comp p (hH.differentiable (by simp) _) (hG.differentiable (by simp) p)]
    change fderiv ℝ H (G p) (fderiv ℝ (standardCrosscap ∘ g) p (![0,1] : Base)) = _
    rw [hGp,fderiv_comp p (standardCrosscap_smooth.differentiable (by simp) _) (hg.differentiable (by simp) p),
      hp,(standardCrosscap_hasFDerivAt 0).fderiv]
    rfl
  have hy : fderiv ℝ g p (![0,1] : Base) 0 = 0 := by
    have hh := hHD.1 (hfirst.symm.trans (hv.trans (map_zero _).symm))
    simpa [standardCrosscapDerivative] using congrArg Prod.snd hh
  have hGv : fderiv ℝ G p (![0,1] : Base) = 0 := by
    change fderiv ℝ (standardCrosscap ∘ g) p (![0,1] : Base) = 0
    rw [fderiv_comp p (standardCrosscap_smooth.differentiable (by simp) _) (hg.differentiable (by simp) p),
      hp,(standardCrosscap_hasFDerivAt 0).fderiv]
    apply Prod.ext
    · ext i; fin_cases i <;> simp [standardCrosscapDerivative]
    · simpa [standardCrosscapDerivative] using hy
  rw [axisDirectionJet_surfaceDirection hφ,axisDirectionJet_congr_germ hEq,
    axisDirectionJet_postcompose hG hH p hGv,hGp]
  exact hHD.comp (crosscap_composed_direction_bijective hg p hp hgD hy)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
