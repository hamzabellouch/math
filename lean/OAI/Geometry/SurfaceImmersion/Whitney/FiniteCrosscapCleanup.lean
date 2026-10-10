import OAI.Geometry.SurfaceImmersion.Geometry.RelativeGlobalCleanPairs
import OAI.Geometry.SurfaceImmersion.Whitney.CleanCrosscapNeighborhoods
import OAI.Geometry.SurfaceImmersion.Geometry.TaylorTargetTranslation

namespace OAI

/-! A prepared finite-crosscap map with global self-transversality and no
additional preimage of any singular point image, preserving every quadratic germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

def QuadraticCrosscapGerms (f : M → ProjectionTarget 3) : Prop :=
  ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
    ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
      p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
      f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
      surfaceDirection φ b (chart q p,t) = 0 ∧
      Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))

theorem clean_finite_quadratic_map {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : QuadraticCrosscapGerms f) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      (∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p) ↔
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) ∧
      (∀ x y, x ≠ y → g x = g y → Function.Surjective (surfacePairDerivative g x y)) ∧
      (∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p) →
        ∀ q, g q = g p → q = p) ∧ QuadraticCrosscapGerms g := by
  classical
  let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
  let : Fintype S := hfin.fintype
  obtain ⟨A,hA,hdis,hAreg⟩ := prepared_clean_crosscap_neighborhoods hfin hrep
  let U : S → Set M := fun i => interior (A i)
  have hIf : ∀ x, x ∉ ⋃ i : S, U i →
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) := by
    intro x hx
    by_contra hbad
    exact hx (mem_iUnion.mpr ⟨⟨x,hbad⟩,(hA ⟨x,hbad⟩).2⟩)
  obtain ⟨g,hg,hfg,_,hI,hreg⟩ := relative_global_clean_pairs hf A U
    (fun i => (hA i).1.isClosed) hdis (fun _ => isOpen_interior)
    (fun _ => interior_subset) hIf S hfin hAreg zero_lt_one
  refine ⟨g,hg,hI,?_,?_,?_⟩
  · intro x y hxy heq
    exact ((mem_cleanSurfacePairs.mp (hreg x y hxy)) heq).2.2
  · intro p hp q heq
    by_contra hqp
    have hpf : p ∈ S := (hI p).not.mp hp
    exact ((mem_cleanSurfacePairs.mp (hreg q p hqp)) heq).2.1 hpf
  · intro p hp
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
