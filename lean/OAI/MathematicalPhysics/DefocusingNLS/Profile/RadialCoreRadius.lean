import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoreFreeIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialBoundaryMonotonicity

namespace OAI

/-! The boundary modulus determines the plateau endpoint of the limiting core. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_core_radius_identification (R ρ l b : ℝ)
    (hρ0 : (3 : ℝ) ≤ ρ) (hl0 : (3 : ℝ) ≤ l) (hρR : ρ < R) (hlR : l ≤ R)
    (hRu : R ≤ (10/3 : ℝ)) (hρwidth : R-ρ ≤ (1/1000 : ℝ))
    (hlwidth : R-l ≤ (1/1000 : ℝ)) (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (A D : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D)
    (hAP : ∀ r ∈ Icc 0 R, 0 < A r)
    (hcore : EqOn A (fun _ => 1) (Icc 0 ρ)) (hDρ : D ρ=0)
    (hAD : ∀ r ∈ Ioo ρ R, HasDerivAt A (D r) r)
    (hDE : ∀ r ∈ Ioo ρ R, HasDerivAt D
      (-11/r*D r-radialAmplitudePotential 6 b A r*A r) r)
    (F G : ℝ → ℂ) (hFc : Continuous F) (hGc : Continuous G)
    (hFI : ∀ r ∈ Icc l R, F r=1+∫ t in l..r, G t)
    (hGI : ∀ r ∈ Icc l R, G r=∫ t in l..r,
      -radialFreeCoefficient t*G t-(b : ℂ)*F t)
    (hB : ∀ r ∈ Icc l R, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2)
    (hboundary : A R=‖F R‖) : ρ=l := by
  obtain ⟨F₀,G₀,hF₀c,hG₀c,hF₀I,hG₀I,hB₀,hmod⟩ := radial_core_free_integral R ρ b hρ0 hρR
    hRu hρwidth hb A D hA hD hAP hcore hDρ hAD hDE
  have heq : ‖F₀ R‖=‖F R‖ := (hmod R ⟨hρR.le,le_rfl⟩).trans hboundary
  rcases lt_trichotomy ρ l with hlt | he | hgt
  · have hn := radial_free_boundary_strict_mono b ρ l R hb hρ0 hRu hlt hlR hρwidth
      F₀ G₀ F G hF₀c hG₀c hFc hGc hF₀I hG₀I hFI hGI hB₀ hB
    exact False.elim ((ne_of_lt hn) heq)
  · exact he
  · have hn := radial_free_boundary_strict_mono b l ρ R hb hl0 hRu hgt hρR.le hlwidth
      F G F₀ G₀ hFc hGc hF₀c hG₀c hFI hGI hF₀I hG₀I hB hB₀
    exact False.elim ((ne_of_lt hn) heq.symm)

end DefocusingNLS

end OAI
