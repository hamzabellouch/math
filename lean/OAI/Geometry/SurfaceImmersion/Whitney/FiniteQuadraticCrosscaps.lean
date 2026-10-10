import OAI.Geometry.SurfaceImmersion.Geometry.FiniteSurfaceReplacement
import OAI.Geometry.SurfaceImmersion.Whitney.RegularCrosscapRepresentatives

namespace OAI

/-! The generic finite singular set can be prepared simultaneously: every
singularity is represented by its genuine second Taylor polynomial, and
no additional singularity is introduced anywhere on the surface. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_finite_quadratic_crosscap_map :
    ∃ F : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F ∧
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F p)}.Finite ∧
      ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F p) →
        ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
          p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
          F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
          surfaceDirection φ b (chart q p,t) = 0 ∧
          Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)) := by
  classical
  obtain ⟨f,hf,hfin,hrep⟩ := exists_regular_crosscap_map (M := M)
  let S : Set M := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
  let : Fintype S := hfin.fintype
  choose q φ b t hp hφ he hz hr using (fun p : S => hrep p p.property)
  obtain ⟨V,hV,hd⟩ := hfin.t2_separation
  have hprep (p : S) := prepare_surface_crosscap hf p (q p) (hp p) p.property
    (hφ p) (he p) (b p) (t p) (hz p) (hr p) (hV p).2 (hV p).1
  choose g hg hs hsub hbad hlocal using hprep
  have hd' : Pairwise fun p r : S => Disjoint (V p) (V r) := by
    intro p r hpr
    exact hd p.property r.property (fun h => hpr (Subtype.ext h))
  obtain ⟨F,hF,hFi,hFe⟩ := finite_disjoint_surface_replacement f hf g hg
    (fun p : S => V p) hs hd'
  have hsing (x : M) :
      (¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F x)) ↔ x ∈ S := by
    constructor
    · intro hx
      by_cases h : ∃ p : S, x ∈ V p
      · obtain ⟨p,hpV⟩ := h
        apply hsub p
        change ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (g p) x)
        intro hgood
        exact hx (by rw [(hFi p x hpV).mfderiv_eq]; exact hgood)
      · have hh : ∀ p : S, x ∉ V p := by simpa only [not_exists] using h
        change ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)
        intro hgood
        exact hx (by rw [(hFe x hh).mfderiv_eq]; exact hgood)
    · intro hx
      let p : S := ⟨x,hx⟩
      rw [(hFi p x (hV p).1).mfderiv_eq]
      exact hbad p
  refine ⟨F,hF,?_,?_⟩
  · have heq : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F p)} = S :=
      Set.ext hsing
    rw [heq]
    exact hfin
  · intro x hx
    let p : S := ⟨x,(hsing x).mp hx⟩
    refine ⟨q p,φ p,b p,t p,hp p,hφ p,?_,hz p,hr p⟩
    exact (hFi p x (hV p).1).trans (hlocal p)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
