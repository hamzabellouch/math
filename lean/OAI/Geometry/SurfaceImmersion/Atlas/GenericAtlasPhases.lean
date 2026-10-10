import OAI.Geometry.SurfaceImmersion.Atlas.GenericPulledPhases
import OAI.Geometry.SurfaceImmersion.Atlas.CenteredAtlasDifferentials

namespace OAI

/-! Generic centered phases in different surface charts. At crossing points
both differentials are pulled to the same actual tangent chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Countable α] [Countable κ]

def centeredAtlasPhase (q : M) (ell : CurvePlane) (L : ℝ) : M → ℝ :=
  centeredConvexPhase ell L (coordinateChart q q) ∘ coordinateChart q

theorem exists_generic_atlas_phases
    (center : ι → M) (L : ι → ℝ) (index : α → ι)
    (u : α → ℝ → CurvePlane) (hu : ∀ a, ContDiff ℝ ∞ (u a))
    (K : α → Set ℝ) (hK : ∀ a, IsCompact (K a))
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
  let c : ι → CurvePlane := fun i => coordinateChart (center i) (center i)
  let A : κ → CurvePlane →L[ℝ] CurvePlane := fun k =>
    fderiv ℝ (coordinateTransition (center (first k)) (base k)) (coordinateChart (base k) (point k))
  let B : κ → CurvePlane →L[ℝ] CurvePlane := fun k =>
    fderiv ℝ (coordinateTransition (center (second k)) (base k)) (coordinateChart (base k) (point k))
  have hA (k : κ) : coordDet (A k) ≠ 0 := coordinateTransition_det_ne _ _
    (coordinateTransition_mem_chart _ _ (hbase k) (hfirst k))
  have hB (k : κ) : coordDet (B k) ≠ 0 := coordinateTransition_det_ne _ _
    (coordinateTransition_mem_chart _ _ (hbase k) (hsecond k))
  have hur (a : α) : ContDiff ℝ ∞ (fun t => u a t-c (index a)) := (hu a).sub contDiff_const
  have hr : ∀ a t, t ∈ K a → deriv (fun t => u a t-c (index a)) t ≠ 0 := by
    intro a t ht
    simpa only [deriv_sub_const] using hregular a t ht
  obtain ⟨ell,hell,he,hn,hcross⟩ := exists_generic_pulled_phases index
    (fun a t => u a t-c (index a)) hur K hK hr (fun a => L (index a))
    first second hdistinct A B hA hB
    (fun k => L (first k) • (coordinateChart (center (first k)) (point k)-c (first k)))
    (fun k => L (second k) • (coordinateChart (center (second k)) (point k)-c (second k))) U hU hne
  refine ⟨ell,hell,he,hn,?_⟩
  intro k
  simp only [centeredAtlasPhase]
  rw [actual_centered_phase_at _ _ _ _ _ (hbase k) (hfirst k),
    actual_centered_phase_at _ _ _ _ _ (hbase k) (hsecond k)]
  exact hcross k

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
