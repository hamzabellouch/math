import OAI.NumberTheory.Ostmann.Supply.UnitProductSize
import OAI.NumberTheory.Ostmann.Supply.UnitWeightPolynomial

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators
open BivariateTruncation
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι→ℕ) [∀i,Fact (p i).Prime]
  (S : ∀i,Finset (ZMod (p i)))

def unitWeightMean (K : ℕ) : ℝ :=
  (Fintype.card (∀i,(ZMod (p i))ˣ):ℝ)⁻¹*
    ∑x:∀i,(ZMod (p i))ˣ,truncatedWeight Finset.univ
      (fun i => localKernel (S i) sparseKernelScale (x i)) K

theorem unitWeightMean_nonneg (K : ℕ) : 0≤unitWeightMean p S K := by
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun x _ => truncatedWeight_nonneg _ _ _))

theorem unitWeightMean_eq_truncation (K : ℕ) :
    (unitWeightMean p S K:ℂ)=rectangularTruncation (unitWeightPolynomial p S) K :=
  (truncation_unitWeightPolynomial p S K).symm

theorem unitWeightMean_error (K : ℕ)
    (hlo : ∀i,(1/3:ℝ)≤density (S i)) (hhi : ∀i,density (S i)≤2/3)
    (hg : ∀i,gamma (S i) ≤ supplyEpsilon^2) :
    |unitWeightMean p S K-(∏i,unitKernelMean (S i) sparseKernelScale)| ≤
      2*Real.exp (8*supplyEpsilon*(∑i,1/(p i:ℝ)))*((103/100:ℝ)⁻¹)^K/
        (1-(103/100:ℝ)⁻¹)^2 := by
  have h := rectangularTruncation_error_le (unitWeightPolynomial p S)
    (by norm_num : (1:ℝ)<103/100)
    (fun u v hu hv => unitWeightPolynomial_norm_uniform p S u v hlo hhi hg hu.le hv.le) K
  rw [←unitWeightMean_eq_truncation,eval_unitWeightPolynomial_one,←Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] at h
  exact h

end Ostmann.Supply

end

end OAI
