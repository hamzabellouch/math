import OAI.NumberTheory.Ostmann.Supply.ActualPrimeLower
import OAI.NumberTheory.Ostmann.Supply.ActualPrimeUpper
import OAI.NumberTheory.Ostmann.Supply.PrimeBandSelection
import OAI.NumberTheory.Ostmann.Supply.PrimeEnumeration

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Supply
open Filter
open scoped BigOperators

theorem nonsparse_supply : NonsparseSupply := by
  classical
  refine ⟨supplyEpsilon^2,by norm_num [supplyEpsilon],?_⟩
  intro d
  have hη : 0<supplyPrimeConstant/2 := div_pos supplyPrimeConstant_pos (by norm_num)
  filter_upwards [exists_sparse_balanced_prime_set d,
    eventually_actualPrime_weight_small d hη,eventually_actualPrime_weight_large,
    eventually_ge_atTop (1:ℝ)] with L hselect hupper hlower hL
  by_contra hnot
  obtain ⟨P,hP,hHlo,hHhi⟩ := hselect (supplyEpsilon^2) ∅ (by simp) (lt_of_not_ge hnot)
  have hpP : ∀q∈P,q.Prime := fun q hq => (hP q hq).1
  let : Fact (∀q∈P,q.Prime) := ⟨hpP⟩
  let p := enumeratePrimes P
  let n := P.card
  have hp : ∀i<n,(p i).Prime := fun i _ => enumeratePrimes_prime P hpP i
  have hinj : Set.InjOn p (Finset.range n:Set ℕ) := enumeratePrimes_injective P
  have hband : ∀i<n,(1/20:ℝ)*L<Real.log (Real.log (p i:ℝ)) ∧
      Real.log (Real.log (p i:ℝ))≤(9/10:ℝ)*L := by
    intro i hi
    have h := hP (p i) (enumeratePrimes_mem P hi)
    exact ⟨h.2.1,h.2.2.1⟩
  have hlo : ∀i<n,(1/3:ℝ)≤density (actualSupport d (p i)) := by
    intro i hi
    have h := (hP (p i) (enumeratePrimes_mem P hi)).2.2.2.1
    simpa only [residueDensityTotal_eq,actualSupport_eq] using h
  have hhi : ∀i<n,density (actualSupport d (p i))≤2/3 := by
    intro i hi
    have h := (hP (p i) (enumeratePrimes_mem P hi)).2.2.2.2.1
    simpa only [residueDensityTotal_eq,actualSupport_eq] using h
  have hg : ∀i<n,gamma (actualSupport d (p i))≤ supplyEpsilon^2 := by
    intro i hi
    have h := (hP (p i) (enumeratePrimes_mem P hi)).2.2.2.2.2.1
    simpa only [residueGamma_eq,actualSupport_eq] using h
  have hHlower : (17/25:ℝ)*L≤reciprocalMass (Finset.range n) p := by
    simpa only [n,p,reciprocalMass_enumeratePrimes] using hHlo
  have hHupper : reciprocalMass (Finset.range n) p≤L := by
    rw [show reciprocalMass (Finset.range n) p=∑q∈P,(1:ℝ)/q from
      reciprocalMass_enumeratePrimes P]
    linarith
  have hn : (n:ℝ)≤Real.exp (Real.exp ((9/10:ℝ)*L)) := primeBand_card_le P
    (fun q hq => ⟨(hP q hq).1,(hP q hq).2.2.1⟩)
  have hbound : ∀i<n,p i≤ supplyPrimeCap L := fun i hi =>
    prime_le_supplyPrimeCap (hp i hi) (hband i hi).2
  let S := fun i => actualSupport d (p i)
  let U := kernelUnitProduct (Finset.range n) p S
  let X := (supplyRadius L)^2
  let W := naturalKernelWeight p S n (supplyTruncation L)
  have hu := hupper p n (fun i => inferInstance) hp hinj hband hlo hhi hg hHlower hHupper hn
  have hl := hlower p n (fun i => inferInstance) hp hinj hbound S hlo hhi hg hHupper
  change (∑q∈primesInInterval (X/2) X,W q)≤
    (supplyPrimeConstant/2)*U*(X:ℝ)/Real.log (X:ℝ) at hu
  change supplyPrimeConstant*U*(X:ℝ)/Real.log (X:ℝ)≤
    ∑q∈primesInInterval (X/2) X,W q at hl
  have hUexp := (kernelUnitProduct_exp_bounds (Finset.range n) p S
    (fun i hi => (hp i (Finset.mem_range.mp hi)).two_le)
    (fun i hi => hlo i (Finset.mem_range.mp hi))
    (fun i hi => hhi i (Finset.mem_range.mp hi))
    (fun i hi => hg i (Finset.mem_range.mp hi))).1
  have hU : 0<U := (Real.exp_pos _).trans_le hUexp
  have hX : (0:ℝ)<X := by exact_mod_cast pow_pos (supplyRadius_pos L) 2
  have hlog : 0<Real.log (X:ℝ) := (Real.exp_pos L).trans_le
    (Ostmann.ZeroDensity.log_supplyPrimeSample_lower L)
  have hpos : 0<supplyPrimeConstant*U*(X:ℝ)/Real.log (X:ℝ) :=
    div_pos (mul_pos (mul_pos supplyPrimeConstant_pos hU) hX) hlog
  have hhalf : (supplyPrimeConstant/2)*U*(X:ℝ)/Real.log (X:ℝ)=
      (supplyPrimeConstant*U*(X:ℝ)/Real.log (X:ℝ))/2 := by ring
  rw [hhalf] at hu
  linarith

end Ostmann.Supply

end

end OAI
