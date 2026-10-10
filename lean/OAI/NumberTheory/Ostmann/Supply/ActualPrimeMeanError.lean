import OAI.NumberTheory.Ostmann.Supply.ConductorBounds
import OAI.NumberTheory.Ostmann.Supply.PrimeMeanIdentity
import OAI.NumberTheory.Ostmann.Supply.PrimePowerTransfer

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Ostmann.ZeroDensity GroupedCharacters MeasureTheory Set
open scoped BigOperators

theorem norm_sum_mul_le_max {α : Type*} [Fintype α] (c e : α→ℂ) {M : ℝ}
    (hc : ∀i,‖c i‖≤M) : ‖∑i,c i*e i‖≤M*∑i,‖e i‖ := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)

theorem actualPrimeMean_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : ℝ} (hL : 1≤L) (hcap : supplyPrimeCap L≤ supplyRadius L) (hR : 2≤ supplyRadius L)
    (p : ι→ℕ) [∀i,Fact (p i).Prime] (hp : Function.Injective p)
    (hbound : ∀i,p i≤ supplyPrimeCap L) (S : ∀i,Finset (ZMod (p i)))
    (hlo : ∀i,(1/3:ℝ)≤density (S i)) (hhi : ∀i,density (S i)≤2/3)
    (hg : ∀i,gamma (S i)≤ supplyEpsilon^2) (hH : (∑i,(1:ℝ)/(p i:ℝ))≤L) :
    |weightedPrimeSum primeWeight (((supplyRadius L)^2:ℕ):ℝ)
        (fun k => truncatedWeight Finset.univ
          (fun i => localKernel (S i) sparseKernelScale (k:ZMod (p i))) (supplyTruncation L))-
      unitWeightMean p S (supplyTruncation L)*(((supplyRadius L)^2:ℕ):ℝ)*
        (∫t in Ioi (0:ℝ),primeWeight t)| ≤
      Real.exp ((Real.log 1200+8*supplyEpsilon)*L)*
        totalPrimitivePrimeError (supplyCharacterCutoff L) none primeWeight (((supplyRadius L)^2:ℕ):ℝ) := by
  classical
  let K := supplyTruncation L
  let pmax := supplyPrimeCap L
  let Q := supplyCharacterCutoff L
  let X : ℝ := (((supplyRadius L)^2:ℕ):ℝ)
  have hmax : 1≤pmax := supplyPrimeCap_pos L
  let b := fun i => localKernel (S i) sparseKernelScale
  let c : PrimitiveFamily Q→ℂ := primitiveCoefficient p hp K pmax hmax hbound b
  let W := fun k : ℕ => truncatedWeight Finset.univ (fun i => b i (k:ZMod (p i))) K
  have hX : 0<X := by dsimp [X]; positivity
  have he : ∀k:ℕ,k.Prime → primeWeight ((k:ℝ)/X)≠0 →
      (W k:ℂ)=∑χ:PrimitiveFamily Q,c χ*χ.2.1 k := by
    intro k hk hφ
    exact primitive_weight_expansion p hp K pmax hmax hbound b k
      (fun i => primeWeight_coprime_local hcap hR hk Fact.out (hbound i) hφ)
  have hid := weightedPrimeSum_sub_main (supplyCharacterCutoff_pos L) c W primeWeight_support hX he
  have hprincipal : c (principalFamily Q (supplyCharacterCutoff_pos L))=(unitWeightMean p S K:ℂ) :=
    actualPrimitiveCoefficient_principal p hp K pmax hmax hbound S
  rw [hprincipal] at hid
  have hnorm := norm_sum_mul_le_max c (fun χ => smoothPrimeError χ.2.1 primeWeight X)
    (norm_primitiveCoefficient_le_exp_band p hp K pmax hmax hbound S hlo hhi hg hL hH)
  rw [←hid,←Complex.ofReal_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hnorm
  change |weightedPrimeSum primeWeight X W-unitWeightMean p S K*X*(∫t in Ioi (0:ℝ),primeWeight t)|≤_
  have heq : unitWeightMean p S K*(X*(∫t in Ioi (0:ℝ),primeWeight t))=
      unitWeightMean p S K*X*(∫t in Ioi (0:ℝ),primeWeight t) := by ring
  rw [heq] at hnorm
  simpa only [totalPrimitivePrimeError,Option.some_ne_none,ite_false] using hnorm

end Ostmann.Supply

end

end OAI
