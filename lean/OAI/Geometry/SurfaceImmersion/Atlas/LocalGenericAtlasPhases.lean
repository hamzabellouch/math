import OAI.Geometry.SurfaceImmersion.Atlas.GenericAtlasPhases
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! Phase selection on compact portions of local boundary arcs. Smooth
extension supplies the global parameter argument without imposing global
chart-domain assumptions on an arc. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Countable α] [Countable κ]

theorem exists_generic_atlas_phases_on
    (center : ι → M) (L : ι → ℝ) (index : α → ι)
    (u : α → ℝ → CurvePlane) (V : α → Set ℝ) (hV : ∀ a, IsOpen (V a))
    (hu : ∀ a, ContDiffOn ℝ ∞ (u a) (V a))
    (K : α → Set ℝ) (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (hregular : ∀ a t, t ∈ K a → deriv (u a) t ≠ 0)
    (first second : κ → ι) (hdistinct : ∀ k, first k ≠ second k)
    (base point : κ → M)
    (hbase : ∀ k, point k ∈ (coordinateChart (base k)).source)
    (hfirst : ∀ k, point k ∈ (coordinateChart (center (first k))).source)
    (hsecond : ∀ k, point k ∈ (coordinateChart (center (second k))).source)
    (U : Set (ι → CurvePlane)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ell ∈ U,
      (∀ a, (K a ∩ {t | deriv (fun s =>
        centeredConvexPhase (ell (index a)) (L (index a))
          (coordinateChart (center (index a)) (center (index a))) (u a s)) t = 0}).Finite) ∧
      (∀ a t, t ∈ K a → deriv (fun s =>
        centeredConvexPhase (ell (index a)) (L (index a))
          (coordinateChart (center (index a)) (center (index a))) (u a s)) t = 0 →
        deriv (deriv (fun s => centeredConvexPhase (ell (index a)) (L (index a))
          (coordinateChart (center (index a)) (center (index a))) (u a s))) t ≠ 0) ∧
      (∀ k, covectorDet
        (phaseDerivative (centeredAtlasPhase (center (first k)) (ell (first k)) (L (first k)) ∘
          (coordinateChart (base k)).symm) (coordinateChart (base k) (point k)))
        (phaseDerivative (centeredAtlasPhase (center (second k)) (ell (second k)) (L (second k)) ∘
          (coordinateChart (base k)).symm) (coordinateChart (base k) (point k))) ≠ 0) := by
  choose W hW hKW hWV v hv he using fun a =>
    CollarVelocity.compact_smooth_extension (hK a) (hV a) (hKV a) (hu a)
  have hsame (a : α) (t : ℝ) (ht : t ∈ K a) : v a =ᶠ[𝓝 t] u a := by
    filter_upwards [(hW a).mem_nhds (hKW a ht)] with s hs
    exact he a hs
  have hreg : ∀ a t, t ∈ K a → deriv (v a) t ≠ 0 := by
    intro a t ht
    rw [(hsame a t ht).deriv_eq]
    exact hregular a t ht
  obtain ⟨ell,hell,hfinite,hn,hcross⟩ := exists_generic_atlas_phases center L index
    v hv K hK hreg first second hdistinct base point hbase hfirst hsecond U hU hne
  let phi (a : α) : CurvePlane → ℝ := centeredConvexPhase (ell (index a)) (L (index a))
    (coordinateChart (center (index a)) (center (index a)))
  have hc (a : α) (t : ℝ) (ht : t ∈ K a) :
      (fun s => phi a (v a s)) =ᶠ[𝓝 t] (fun s => phi a (u a s)) :=
    (hsame a t ht).fun_comp (phi a)
  refine ⟨ell,hell,?_,?_,hcross⟩
  · intro a
    apply (hfinite a).subset
    rintro t ⟨ht,hzero⟩
    exact ⟨ht,(hc a t ht).deriv_eq.trans hzero⟩
  · intro a t ht hzero
    change deriv (deriv (fun s => phi a (u a s))) t ≠ 0
    rw [← (hc a t ht).deriv.deriv_eq]
    apply hn a t ht
    exact (hc a t ht).deriv_eq.trans hzero

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
