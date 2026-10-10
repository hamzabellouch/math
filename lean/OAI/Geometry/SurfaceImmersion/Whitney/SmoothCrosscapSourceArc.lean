import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapPathInterior
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPathRegularInterior
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceRegularLocus

namespace OAI

/-! An actual smooth embedded source arc joining the two crosscaps. Its
interior is regular, and every newly inserted point lies in a compact
regular set, so the original endpoint geometry remains accessible. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem smooth_crosscap_source_arc
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hgood : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2 ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).1) ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).2))
    (hsing : ∀ x, f x = f p → x = p) :
    ∃ (P : SmoothCompactArc planeModel M) (K : Set M),
      IsCompact K ∧ K ⊆ {x | Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)} ∧
      P.curve P.start = p ∧ P.curve P.finish = q ∧
      P.curve '' Icc P.start P.finish ⊆ Prod.fst '' range Γ ∪ K ∧
      ∀ t ∈ Ioo P.start P.finish,
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P.curve t)) := by
  obtain ⟨γ,hγ,hiγ,himage,hregular⟩ := crosscap_source_embedded_path_regular hf hreg
    cp cq hΓ hi hzero hone heq hgood hsing
  let O := {x | Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)}
  have hO : IsOpen O := surface_regular_locus_open hf
  have hγO : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ O := by
    intro t ht
    let u : I := ⟨t,ht.1.le,ht.2.le⟩
    have he : γ.extend t = γ u := Path.extend_extends' γ u
    rw [he]
    exact hregular u ht.1 ht.2
  obtain ⟨P,K,hK,hKO,hPs,hPf,hPi⟩ := smooth_finite_regular_path hγ hiγ hO hγO
  refine ⟨P,K,hK,hKO,hPs,hPf,?_,?_⟩
  · intro x hx
    rcases hPi hx with h | h
    · exact Or.inl (himage h)
    · exact Or.inr h
  · exact smoothed_arc_interior hregular P hKO hPs hPf hPi

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
