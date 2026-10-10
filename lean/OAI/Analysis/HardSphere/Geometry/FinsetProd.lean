import Mathlib
import OAI.Analysis.HardSphere.Geometry.SmoothMultiplier
import OAI.Analysis.HardSphere.Geometry.TorusLiftBox

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def SmoothMultiplier.finsetProd {S : Type*} [DecidableEq S] {n : ℕ} {L : Length}
    (A : Finset S) (w : S → SmoothMultiplier n L) : SmoothMultiplier n L :=
  .ofSmooth (fun X ↦ ∏ s∈A, (w s).toFun X) (contDiff_prod fun s _ ↦ (w s).smooth)

lemma SmoothMultiplier.partial_finsetProd {S : Type*} [DecidableEq S] {n : ℕ} {L : Length}
    (A : Finset S) (w : S → SmoothMultiplier n L) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (SmoothMultiplier.finsetProd A w).toFun p X=
      ∑ s∈A, (∏ z∈A.erase s, (w z).toFun X)*coordDerivative n L (w s).toFun p X := by
  unfold coordDerivative
  change (fderiv ℝ (fun Y ↦ ∏ s∈A, (w s).toFun (project n L Y)) _) _ = _
  rw [fderiv_finsetProd (fun s _ ↦ (w s).smooth.differentiable (by simp) _),sum_apply]
  simp only [smul_apply,smul_eq_mul,project_representative]

lemma norm_sq_sum_of_disjoint {S : Type*} [DecidableEq S] (A : Finset S) (f : S → ℂ)
    (hf : ∀ s∈A, ∀ z∈A, s≠z → f s=0 ∨ f z=0) : ‖∑ s∈A, f s‖^2=∑ s∈A, ‖f s‖^2 := by
  by_cases h : ∃ s∈A, f s≠0
  · obtain ⟨s,hs,hfs⟩ := h
    have hz : ∀ z∈A, z≠s → f z=0 := by
      intro z hz hzs
      exact (hf z hz s hs hzs).resolve_right hfs
    rw [Finset.sum_eq_single s (fun z hza hzs ↦ hz z hza hzs) (by simp_all)]
    rw [Finset.sum_eq_single s (fun z hza hzs ↦ by rw [hz z hza hzs,norm_zero]; norm_num) (by simp_all)]
  · push Not at h
    rw [Finset.sum_eq_zero (fun s hs ↦ h s hs)]
    simp only [norm_zero,zero_pow (by norm_num : 2≠0)]
    symm
    exact Finset.sum_eq_zero fun s hs ↦ by rw [h s hs,norm_zero]; norm_num

end HardSphere

end

end OAI
