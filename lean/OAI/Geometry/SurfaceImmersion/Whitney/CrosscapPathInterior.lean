import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapSourceEmbeddedPath

namespace OAI

/-! The embedded source path obtained by loop removal meets no other
singular point: every interior point belongs to a regular original sheet. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem crosscap_source_embedded_path_regular
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
    ∃ P : Path p q, FiniteRegularPath planeModel P ∧ Function.Injective P ∧
      range P ⊆ Prod.fst '' range Γ ∧
      ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 →
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P t)) := by
  obtain ⟨P,hPp,hPi,hPr⟩ := crosscap_source_embedded_path hf hreg cp cq hΓ hi hzero hone heq hgood hsing
  refine ⟨P,hPp,hPi,hPr,?_⟩
  intro t ht0 ht1
  obtain ⟨z,⟨u,hu⟩,hz⟩ := hPr (mem_range_self t)
  have hpnt : (Γ u).1 = P t := by rw [hu]; exact hz
  have hu0 : u ≠ 0 := by
    intro he
    have htzero : t = 0 := hPi (by rw [Path.source,← hpnt,he,hzero])
    have hval := congrArg (fun s : I => (s:ℝ)) htzero
    change (t:ℝ) = 0 at hval
    linarith
  have hu1 : u ≠ 1 := by
    intro he
    have htone : t = 1 := hPi (by rw [Path.target,← hpnt,he,hone])
    have hval := congrArg (fun s : I => (s:ℝ)) htone
    change (t:ℝ) = 1 at hval
    linarith
  have hu0' : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm))
  have hu1' : (u:ℝ) < 1 := lt_of_le_of_ne u.property.2 (fun he => hu1 (Subtype.ext he))
  rw [← hpnt]
  exact (hgood u hu0' hu1').2.1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
