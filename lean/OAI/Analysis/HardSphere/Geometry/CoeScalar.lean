import Mathlib
import OAI.Analysis.HardSphere.Geometry.InnerClmRealRight
import OAI.Analysis.HardSphere.Geometry.NormSqIntegral
import OAI.Analysis.HardSphere.Geometry.SmoothMultiplier

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

lemma SmoothMultiplier.coe_onScalar {n : ℕ} {L : Length} (f : SmoothMultiplier n L) (u : ScalarL2 n L) :
    f.onScalar u =ᵐ[volume] fun X ↦ f.toFun X*u X := L2Multiplier.coe_clm _ _ _

lemma SmoothMultiplier.coe_derivativeScalar {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (p : Direction n) (u : ScalarL2 n L) :
    f.derivativeScalar p u =ᵐ[volume] fun X ↦ coordDerivative n L f.toFun p X*u X :=
  L2Multiplier.coe_clm _ _ _

lemma SmoothMultiplier.gradient_norm_le {S : Type*} {n : ℕ} {L : Length}
    (A : Finset S) (f : SmoothMultiplier n L) (g : S → SmoothMultiplier n L) (C : ℝ)
    (hfg : ∀ X, (∑ p : Direction n, ‖coordDerivative n L f.toFun p X‖^2) ≤
      C*∑ s∈A, ‖(g s).toFun X‖^2) (u : ScalarL2 n L) :
    (∑ p : Direction n, ‖f.derivativeScalar p u‖^2) ≤ C*∑ s∈A, ‖(g s).onScalar u‖^2 := by
  have hi (p : Direction n) : Integrable (fun X ↦ ‖(f.derivativeScalar p u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  have hj (s : S) : Integrable (fun X ↦ ‖((g s).onScalar u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  simp_rw [IndicatorStrong.norm_sq_integral]
  rw [← integral_finsetSum Finset.univ (fun p _ ↦ hi p),
    ← integral_finsetSum A (fun s _ ↦ hj s),← integral_const_mul]
  apply integral_mono_ae (integrable_finsetSum _ (fun p _ ↦ hi p))
    ((integrable_finsetSum _ (fun s _ ↦ hj s)).const_mul C)
  have hd : ∀ᵐ X ∂volume, ∀ p, (f.derivativeScalar p u) X=coordDerivative n L f.toFun p X*u X :=
    ae_all_iff.mpr (fun p ↦ f.coe_derivativeScalar p u)
  have hg : ∀ᵐ X ∂volume, ∀ s∈A, ((g s).onScalar u) X=(g s).toFun X*u X :=
    (ae_ball_iff A.countable_toSet).mpr (fun s _ ↦ (g s).coe_onScalar u)
  filter_upwards [hd,hg] with X hX hY
  simp_rw [hX,norm_mul,mul_pow]
  have he : (∑ s∈A, ‖((g s).onScalar u) X‖^2)=
      (∑ s∈A, ‖(g s).toFun X‖^2)*‖u X‖^2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s hs ↦ by rw [hY s hs,norm_mul,mul_pow]
  rw [he,← Finset.sum_mul,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hfg X) (sq_nonneg _)

end HardSphere

end

end OAI
