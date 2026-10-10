import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseCover
import OAI.Geometry.SurfaceImmersion.Geometry.SplitSupportedTarget

namespace OAI

/-! Split an actual compact target into geometrically admissible phase pieces. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes
open JetPolynomial (SupportedField)
open PhaseMean (ComplexTensor)

/-- Every supported target with a good phase on its support admits a finite
exact decomposition into targets for actual compactly bounded good charts. -/
theorem split_target_into_good_phase_charts {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts Base)
    (hImm : ∀ p ∈ (K : Set Base), Function.Injective (fderiv ℝ F p))
    (hgood : ∀ p ∈ (K : Set Base), Good (realSecondTensor F p) (phaseDerivative φ p))
    (A : SupportedField (F := ComplexTensor) K) :
    ∃ (t : Finset K) (c : t → GoodPhaseChart F φ) (L : t → Compacts Base)
      (B : (i : t) → SupportedField (F := ComplexTensor) (L i)),
      (∀ i, (L i : Set Base) ⊆ K) ∧
      (∀ i, (L i : Set Base) ⊆ (c i).chart.source) ∧
      (∀ x, ∑ i, B i x = A x) := by
  classical
  obtain ⟨t,c,hcover⟩ := finite_good_phase_cover hF hφ K hImm hgood
  obtain ⟨L,B,hLK,hLB,hsum⟩ := PhasePartitions.exists_split_supported_complex_target
    K (fun i : t => (c i).chart.source) (fun i => (c i).chart.open_source) hcover A
  exact ⟨t,c,L,B,hLK,hLB,hsum⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
