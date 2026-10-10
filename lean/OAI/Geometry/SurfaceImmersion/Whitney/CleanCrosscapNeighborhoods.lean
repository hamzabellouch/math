import OAI.Geometry.SurfaceImmersion.Whitney.PreparedCrosscapNeighborhoods
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapFiberIsolation
import OAI.Geometry.SurfaceImmersion.Whitney.CleanSurfacePairs

namespace OAI

/-! Frozen crosscap neighborhoods may be chosen so their internal double
pairs are transverse and involve no singular point. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_clean_crosscap_neighborhoods
    {f : M → ProjectionTarget 3}
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
    ∃ A : S → Set M, (∀ i, IsCompact (A i) ∧ i.val ∈ interior (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → (x,y) ∈ cleanSurfacePairs f S := by
  classical
  dsimp only
  let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
  obtain ⟨A,hA,hdis,hreg⟩ := prepared_crosscap_neighborhoods hfin hrep
  have hex (i : S) : ∃ B : Set M, IsCompact B ∧ i.val ∈ interior B ∧ B ⊆ A i ∧
      ∀ x ∈ B, f x = f i.val → x = i.val := by
    obtain ⟨q,φ,b,t,hpq,hφ,he,hz,hR⟩ := hrep i.val i.property
    obtain ⟨U,hU,hiU,hiso⟩ := prepared_crosscap_isolated_fiber i.val q hpq hφ he b t hz hR
    obtain ⟨B,hB,hiB,hBU⟩ := exists_compact_subset (isOpen_interior.inter hU) ⟨(hA i).2,hiU⟩
    exact ⟨B,hB,hiB,fun x hx => interior_subset (hBU hx).1,
      fun x hx => hiso x (hBU hx).2⟩
  choose B hB hiB hBA hIso using hex
  have honly (i : S) (x : M) (hx : x ∈ B i) (hxS : x ∈ S) : x = i.val := by
    by_contra hne
    let j : S := ⟨x,hxS⟩
    have hij : i ≠ j := fun h => hne (congrArg Subtype.val h).symm
    exact (Set.disjoint_left.mp (hdis hij)) (hBA i hx) (interior_subset (hA j).2)
  refine ⟨B,fun i => ⟨hB i,hiB i⟩,?_,?_⟩
  · intro i j hij
    exact (hdis hij).mono (hBA i) (hBA j)
  · intro i x hx y hy hxy
    apply mem_cleanSurfacePairs.mpr
    intro heq
    refine ⟨?_,?_,(hreg i x (hBA i hx) y (hBA i hy) hxy).resolve_left (not_not.mpr heq)⟩
    · intro hxS
      have hxi := honly i x hx hxS
      have hyi : y = i.val := hIso i y hy (heq.symm.trans (congrArg f hxi))
      exact hxy (hxi.trans hyi.symm)
    · intro hyS
      have hyi := honly i y hy hyS
      have hxi : x = i.val := hIso i x hx (heq.trans (congrArg f hyi))
      exact hxy (hxi.trans hyi.symm)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
