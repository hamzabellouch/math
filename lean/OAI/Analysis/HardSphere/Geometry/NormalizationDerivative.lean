import Mathlib
import OAI.Analysis.HardSphere.Collisions.NormalizedInsertion
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

lemma SmoothMultiplier.normalization_derivative_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hp : ∀ Y, 0<f.fiberMass Y) (p : Direction (n+1)) (Y : Configuration n L) :
    f.fiberMass Y * (∫ x : Torus L,
      ‖coordDerivative (n+1) L (f.normalization hr hp).toFun p (Fin.cons x Y)‖^2) ≤
      ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
  have he : (fun X ↦ (f.normalization hr hp).toFun X *
      (f.massRoot hr hp).toFun (Fin.tail X))=f.toFun := by
    funext X
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp _)).ne')
  have hh := (f.normalization hr hp).fiber_derivative_mul_tail_le (f.massRoot hr hp)
    (f.normalization_real hr hp) (f.normalization_norm hr hp) p Y
  rw [he] at hh
  have hn : ‖(f.massRoot hr hp).toFun Y‖^2=f.fiberMass Y := by
    change ‖(Real.sqrt (f.fiberMass Y) : ℂ)‖^2=_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hp Y).le]
  rwa [hn] at hh

lemma SmoothMultiplier.insertion_from_raw {n : ℕ} {L : Length} {a C z : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hz : 0<z)
    (hZ : ∀ Y : Configuration n L, z≤f.fiberMass Y)
    (hC : ∀ Y : Configuration n L,
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C)
    {u : Jet n L} (hu : u∈dirichletDomain n L a) :
    ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L a ∧
      ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C/z)*‖u.1‖^2 := by
  have hp : ∀ Y, 0<f.fiberMass Y := fun Y ↦ hz.trans_le (hZ Y)
  refine ⟨(f.normalization hr hp).insertionJet u,?_⟩
  refine (f.normalization hr hp).normalized_insertion (f.normalization_clearance hr hp hc)
    (f.normalization_real hr hp) (f.normalization_norm hr hp) ?_ hu
  intro Y
  rw [le_div_iff₀ hz,mul_comm]
  calc
    z * ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L (f.normalization hr hp).toFun p (Fin.cons x Y)‖^2 ≤
      f.fiberMass Y * ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L (f.normalization hr hp).toFun p (Fin.cons x Y)‖^2 := by
      apply mul_le_mul_of_nonneg_right (hZ Y)
      exact Finset.sum_nonneg fun p _ ↦ integral_nonneg fun x ↦ sq_nonneg _
    _ ≤ ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun p _ ↦ f.normalization_derivative_le hr hp p Y
    _ ≤ C := hC Y

end HardSphere

end

end OAI
