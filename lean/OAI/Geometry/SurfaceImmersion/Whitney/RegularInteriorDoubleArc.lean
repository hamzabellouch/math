import OAI.Geometry.SurfaceImmersion.Whitney.SmoothInteriorDoubleArc
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleArcProjections

namespace OAI

/-! The smoothed interior of a simple crosscap-connecting double arc has
regular projections to both source sheets and a regular common image. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

theorem regular_interior_double_arc
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hgood : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2 ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ t).1) ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ t).2))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ P : SmoothDoubleArc f,
      P.arc.curve '' Icc P.arc.start P.arc.finish =
        Γ '' {t : I | a ≤ (t:ℝ) ∧ (t:ℝ) ≤ b} ∧
      P.arc.curve P.arc.start = Γ ⟨a,⟨ha.le,(hab.trans hb).le⟩⟩ ∧
      P.arc.curve P.arc.finish = Γ ⟨b,⟨(ha.trans hab).le,hb.le⟩⟩ ∧
      ∀ t ∈ Icc P.arc.start P.arc.finish,
        Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun u => (P.arc.curve u).1) t) ∧
        Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun u => (P.arc.curve u).2) t) ∧
        Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,ProjectionTarget 3) (fun u => f (P.arc.curve u).1) t) := by
  obtain ⟨P,hPi,hPl,hPr⟩ := smooth_interior_double_arc hf hreg hΓ hinj heq
    (fun t ht0 ht1 => (hgood t ht0 ht1).1) ha hab hb
  refine ⟨P,hPi,hPl,hPr,?_⟩
  intro t ht
  obtain ⟨u,hu,heu⟩ := hPi.subset ⟨t,ht,rfl⟩
  have hgu := hgood u (ha.trans_le hu.1) (hu.2.trans_lt hb)
  apply P.regular_projections hf (P.arc.interval_subset ht)
  · rw [← heu]
    exact hgu.2.1
  · rw [← heu]
    exact hgu.2.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
