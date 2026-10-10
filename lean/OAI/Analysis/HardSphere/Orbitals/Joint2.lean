import Mathlib
import OAI.Analysis.HardSphere.Orbitals.Joint
import OAI.Analysis.HardSphere.Geometry.CoeScalar

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
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma joint_support {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} {h : ℝ} (hh : 0<h)
    (c : S → Torus L) (A : Finset S) (u : ScalarL2 n L) :
    ∀ᵐ X ∂volume, ((joint n L c h A).onScalar u) X≠0 → ∀ s∈A, count L (1/100) (c s) X ≤ 2*h := by
  filter_upwards [(joint n L c h A).coe_onScalar u] with X hX hu s hs
  have hj : (joint n L c h A).toFun X≠0 := fun hz ↦ hu (by rw [hX,hz,zero_mul])
  rw [joint_apply] at hj
  have he : (profile h (count L (1/100) (c s) X) : ℂ)≠0 :=
    (Finset.prod_ne_zero_iff.mp hj) s hs
  by_contra hn
  have hz := profile_zero hh (le_of_lt (not_le.mp hn))
  exact he (by rw [hz,Complex.ofReal_zero])

lemma joint_gradient_norm_le {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} {h M : ℝ}
    (hh : 0<h) (hM : 0 ≤ M) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M)
    (c : S → Torus L) (hc : ∀ z v, z≠v → 1 ≤ dist (c z) (c v))
    (A : Finset S) (u : ScalarL2 n L) :
    (∑ p : Direction n, ‖(joint n L c h A).derivativeScalar p u‖^2) ≤
      ((2*M^2*(3*(4*(24*Real.pi^2*M^2/(8*(1/100))^2))))/h)*
        ∑ s∈A, ‖(joint n L c h (A.erase s)).onScalar u‖^2 :=
  SmoothMultiplier.gradient_norm_le A _ _ _ (joint_gradient_le hh hM hb c hc A) u

end HardSphere.CellOrbital

end

end OAI
