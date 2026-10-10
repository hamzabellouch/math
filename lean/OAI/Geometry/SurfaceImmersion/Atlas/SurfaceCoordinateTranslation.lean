import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceScalarRepresentative

namespace OAI

/-! Exact coordinate representatives of scalar-weighted surface translations. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surface_translation_chart_germ (p : M) {x : M}
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    {F : Base → ProjectionTarget 3} {ρ : Base → ℝ}
    (hF : f =ᶠ[𝓝 x] F ∘ chart p) (hρ : χ =ᶠ[𝓝 x] ρ ∘ chart p)
    (a : ProjectionTarget 3) :
    surfaceTranslation f χ a =ᶠ[𝓝 x] (fun z => F z+ρ z • a) ∘ chart p := by
  filter_upwards [hF,hρ] with y hy hρy
  change f y+χ y • a = F (chart p y)+ρ (chart p y) • a
  rw [hy,hρy]
  rfl

theorem surface_pair_translation_coordinate_iff (p q : M) {x y : M}
    (hx : x ∈ (chart p).source) (hy : y ∈ (chart q).source)
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    {F G : Base → ProjectionTarget 3} {ρ σ : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hρ : ContDiff ℝ ∞ ρ) (hσ : ContDiff ℝ ∞ σ)
    (heF : f =ᶠ[𝓝 x] F ∘ chart p) (heG : f =ᶠ[𝓝 y] G ∘ chart q)
    (heρ : χ =ᶠ[𝓝 x] ρ ∘ chart p) (heσ : χ =ᶠ[𝓝 y] σ ∘ chart q)
    (a : ProjectionTarget 3) :
    Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) x y) ↔
      Function.Surjective (fderiv ℝ
        (fun z : Base × Base => (F z.1-G z.2)+(ρ z.1-σ z.2) • a)
        (chart p x,chart q y)) := by
  have h := surface_pair_coordinate_regular_iff p q hx hy
    (hF.add (hρ.smul contDiff_const)) (hG.add (hσ.smul contDiff_const))
    (surface_translation_chart_germ p heF heρ a) (surface_translation_chart_germ q heG heσ a)
  have heq : (fun z : Base × Base => (F z.1+ρ z.1 • a)-(G z.2+σ z.2 • a)) =
      (fun z : Base × Base => (F z.1-G z.2)+(ρ z.1-σ z.2) • a) := by
    funext z
    rw [sub_smul]
    abel
  change Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) x y) ↔
    Function.Surjective (fderiv ℝ (fun z : Base × Base =>
      (F z.1+ρ z.1 • a)-(G z.2+σ z.2 • a)) (chart p x,chart q y)) at h
  rwa [heq] at h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
