import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildModel

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

def angular (p : Exterior) : Sphere := p.2

def firstCoordinate : E3 →L[ℝ] ℝ := EuclideanSpace.proj ⟨0, Nat.zero_lt_succ 2⟩

lemma extChart_formula (p y : Exterior) : extChartAt I3 p y = join (height y,chartAt E2 p.2 y.2) := rfl
lemma inverseChart_height (p : Exterior) {z : E3} (hz : z ∈ range I3) :
    height ((extChartAt I3 p).symm z) = z 0 := by
  change (I3.symm z).val 0 = z 0
  exact congrArg (fun w : E3 => w 0) (I3.right_inv hz)
lemma inverseChart_angular (p : Exterior) {z : E3} (hz : z ∈ range I3) :
    angular ((extChartAt I3 p).symm z) = (chartAt E2 p.2).symm (dropPlane z) := by
  change (chartAt E2 p.2).symm (dropPlane (I3.symm z).val) = _
  rw [show (I3.symm z).val = z from I3.right_inv hz]

lemma angular_chart_eq (p : Exterior) :
    writtenInExtChartAt I3 I2 p angular =ᶠ[𝓝[range I3] extChartAt I3 p p] dropPlane := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I3) p] with z hz
  have hzr := extChartAt_target_subset_range (I := I3) p hz
  have hz' : dropPlane z ∈ (chartAt E2 p.2).target := by
    have h := (extChartAt I3 p).map_target hz
    have hi := (extChartAt I3 p).right_inv hz
    rw [extChart_formula] at hi
    have hh := congrArg dropPlane hi
    simp only [drop_join] at hh
    rw [← hh]
    apply (chartAt E2 p.2).map_source
    rw [extChartAt_source] at h
    change (extChartAt I3 p).symm z ∈ (productChart p.2).source at h
    simpa only [productChart_source, mem_preimage] using h
  change chartAt E2 p.2 (angular ((extChartAt I3 p).symm z)) = _
  rw [inverseChart_angular p hzr,(chartAt E2 p.2).right_inv hz']

lemma height_chart_eq (p : Exterior) :
    writtenInExtChartAt I3 𝓘(ℝ,ℝ) p height =ᶠ[𝓝[range I3] extChartAt I3 p p] firstCoordinate := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact inverseChart_height p hz

lemma angular_chart_self (p : Exterior) :
    writtenInExtChartAt I3 I2 p angular (extChartAt I3 p p) = dropPlane (extChartAt I3 p p) := by
  change chartAt E2 p.2 (angular ((extChartAt I3 p).symm (extChartAt I3 p p))) = _
  rw [extChartAt_to_inv,extChart_formula,drop_join]
  rfl
lemma height_chart_self (p : Exterior) :
    writtenInExtChartAt I3 𝓘(ℝ,ℝ) p height (extChartAt I3 p p) = firstCoordinate (extChartAt I3 p p) := by
  exact inverseChart_height p (extChartAt_target_subset_range (I := I3) p (mem_extChartAt_target p))

lemma angular_smooth : ContMDiff I3 I2 ∞ angular := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuous_snd.continuousAt,?_⟩
  exact dropPlane.contDiff.contDiffWithinAt.congr_of_eventuallyEq (angular_chart_eq p) (angular_chart_self p)
lemma height_smooth : ContMDiff I3 𝓘(ℝ,ℝ) ∞ height := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(continuous_subtype_val.comp continuous_fst).continuousAt,?_⟩
  exact firstCoordinate.contDiff.contDiffWithinAt.congr_of_eventuallyEq (height_chart_eq p) (height_chart_self p)
lemma mfderiv_angular (p : Exterior) : mfderiv I3 I2 angular p = dropPlane := by
  apply HasMFDerivAt.mfderiv
  refine ⟨continuous_snd.continuousAt,?_⟩
  exact dropPlane.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq (angular_chart_eq p) (angular_chart_self p)
lemma mfderiv_height (p : Exterior) : mfderiv I3 𝓘(ℝ,ℝ) height p = firstCoordinate := by
  apply HasMFDerivAt.mfderiv
  refine ⟨(continuous_subtype_val.comp continuous_fst).continuousAt,?_⟩
  exact firstCoordinate.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq (height_chart_eq p) (height_chart_self p)

end CKSSchwarzschild

end

end OAI
