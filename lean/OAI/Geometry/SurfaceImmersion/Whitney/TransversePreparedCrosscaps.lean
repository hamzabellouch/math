import OAI.Geometry.SurfaceImmersion.Geometry.RelativeGlobalTransversality
import OAI.Geometry.SurfaceImmersion.Whitney.PreparedCrosscapNeighborhoods
import OAI.Geometry.SurfaceImmersion.Geometry.TaylorTargetTranslation

namespace OAI

/-! The previously constructed finite-crosscap map can be made globally
self-transverse away from its diagonal, preserving every quadratic germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_transverse_prepared_crosscap_map :
    ∃ f : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f ∧
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite ∧
      (∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y)) ∧
      ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
        ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
          p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
          f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
          surfaceDirection φ b (chart q p,t) = 0 ∧
          Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)) := by
  classical
  obtain ⟨f,hf,hfin,hrep⟩ := exists_finite_quadratic_crosscap_map (M := M)
  let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
  let : Fintype S := hfin.fintype
  obtain ⟨A,hA,hdis,hAreg⟩ := prepared_crosscap_neighborhoods hfin hrep
  let U : S → Set M := fun i => interior (A i)
  have hIf : ∀ x, x ∉ ⋃ i : S, U i →
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) := by
    intro x hx
    by_contra hbad
    exact hx (mem_iUnion.mpr ⟨⟨x,hbad⟩,(hA ⟨x,hbad⟩).2⟩)
  obtain ⟨g,hg,hfg,_,hI,hreg⟩ := relative_global_transversality hf A U
    (fun i => (hA i).1.isClosed) hdis (fun _ => isOpen_interior)
    (fun _ => interior_subset) hIf hAreg zero_lt_one
  have hsing : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p)} = S := by
    ext p
    exact (hI p).not
  refine ⟨g,hg,by simpa only [hsing] using hfin,hreg,?_⟩
  intro p hp
  have hpf : p ∈ S := by exact (hI p).not.mp hp
  obtain ⟨q,φ,b,t,hpq,hφ,he,hz,hr⟩ := hrep p hpf
  obtain ⟨a,ha⟩ := hfg ⟨p,hpf⟩
  have hpa : p ∈ A ⟨p,hpf⟩ := interior_subset (hA ⟨p,hpf⟩).2
  have htrans : g =ᶠ[𝓝 p] (fun x => f x+a) := ha.filter_mono (nhds_le_nhdsSet hpa)
  refine ⟨q,(fun x => φ x+a),b,t,hpq,hφ.add contDiff_const,?_,?_,?_⟩
  · rw [centeredSurfaceTaylor_add_const]
    filter_upwards [htrans,he] with x hx hex
    change g x = centeredSurfaceTaylor φ (chart q p) (chart q x)+a
    rw [hx,hex]
    rfl
  · rwa [surfaceDirection_add_const]
  · rwa [surfaceDirection_add_const]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
