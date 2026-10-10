import OAI.Geometry.SurfaceImmersion.Whitney.UnorderedDoubleCurveChart
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapHalfLineChart
import OAI.Geometry.SurfaceImmersion.Whitney.TransversePreparedCrosscaps

namespace OAI

/-! An unconditional compact double curve with genuine line charts in
its interior and half-line charts at precisely its finite diagonal set. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

def doubleCurveBoundary (f : M → ProjectionTarget 3) : Set (compactifiedDoubleCurve f) :=
  {z | ∃ p, unorderedPair (p,p) = z.val}

omit [T2Space M] in
theorem doubleCurveBoundary_finite {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite) :
    (doubleCurveBoundary f).Finite := by
  have hD := compactifiedDoubleCurve_finite_diagonal hf hfin
  apply Set.Finite.of_finite_image (f := fun z : compactifiedDoubleCurve f => z.val)
  · apply hD.subset
    rintro z ⟨w,hw,rfl⟩
    exact ⟨w.property,hw⟩
  · exact Subtype.val_injective.injOn

theorem transverse_double_curve_interior_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (z : compactifiedDoubleCurve f) (hz : z ∉ doubleCurveBoundary f) :
    ∃ c : OpenPartialHomeomorph (compactifiedDoubleCurve f) ℝ, z ∈ c.source := by
  obtain ⟨w,hw,hew⟩ := z.property
  have hne : w.1 ≠ w.2 := by
    intro he
    apply hz
    refine ⟨w.1,?_⟩
    have hw' : (w.1,w.1) = w := Prod.ext rfl he
    rw [hw',hew]
  have heq := doublePairs_closure_equal hf.continuous hw
  obtain ⟨c,hc⟩ := unordered_double_curve_chart hf w.1 w.2 hne heq (hreg _ _ hne heq)
  refine ⟨c,?_⟩
  have hz' : (⟨unorderedPair (w.1,w.2),⟨(w.1,w.2),subset_closure ⟨hne,heq⟩,rfl⟩⟩ : compactifiedDoubleCurve f) = z :=
    Subtype.ext hew
  rwa [hz'] at hc

theorem transverse_double_curve_boundary_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    (z : compactifiedDoubleCurve f) (hz : z ∈ doubleCurveBoundary f) :
    ∃ c : OpenPartialHomeomorph (compactifiedDoubleCurve f) (Ici (0:ℝ)),
      z ∈ c.source ∧ c z = ⟨0,by simp⟩ := by
  obtain ⟨p,hp⟩ := hz
  have hpK : unorderedPair (p,p) ∈ compactifiedDoubleCurve f := hp.symm ▸ z.property
  have hs : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) :=
    doublePairs_closure_diagonal_singular hf p ((compactifiedDoubleCurve_diagonal f p).mp hpK)
  obtain ⟨q,φ,b,t,hpq,hφ,he,hzero,hR⟩ := hrep p hs
  obtain ⟨c,hmem,hc,hc0⟩ := crosscap_half_line_chart hf p q hpq hφ he b t hzero hR
  have hez : (⟨unorderedPair (p,p),hmem⟩ : compactifiedDoubleCurve f) = z := Subtype.ext hp
  exact ⟨c,hez ▸ hc,hez ▸ hc0⟩

variable [CompactSpace M]

theorem exists_compact_double_curve_charts :
    ∃ f : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f ∧
      IsCompact (compactifiedDoubleCurve f) ∧ (doubleCurveBoundary f).Finite ∧
      (∀ z : compactifiedDoubleCurve f, z ∉ doubleCurveBoundary f →
        ∃ c : OpenPartialHomeomorph (compactifiedDoubleCurve f) ℝ, z ∈ c.source) ∧
      (∀ z : compactifiedDoubleCurve f, z ∈ doubleCurveBoundary f →
        ∃ c : OpenPartialHomeomorph (compactifiedDoubleCurve f) (Ici (0:ℝ)),
          z ∈ c.source ∧ c z = ⟨0,by simp⟩) := by
  obtain ⟨f,hf,hfin,hreg,hrep⟩ := exists_transverse_prepared_crosscap_map (M := M)
  exact ⟨f,hf,compactifiedDoubleCurve_compact f,doubleCurveBoundary_finite hf hfin,
    transverse_double_curve_interior_chart hf hreg,transverse_double_curve_boundary_chart hf hrep⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
