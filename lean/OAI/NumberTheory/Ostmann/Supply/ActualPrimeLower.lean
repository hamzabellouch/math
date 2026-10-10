import OAI.NumberTheory.Ostmann.Supply.ActualPrimeMeanError
import OAI.NumberTheory.Ostmann.Supply.PrimeMeanBounds
import OAI.NumberTheory.Ostmann.Supply.PrimeMeanScale
import OAI.NumberTheory.Ostmann.Supply.WeightFiniteIndex
import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyPrimeError

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Supply
open Filter MeasureTheory Set
open scoped BigOperators

def supplyPrimeConstant : ℝ := (∫t in Ioi (0:ℝ),primeWeight t)/4

theorem supplyPrimeConstant_pos : 0<supplyPrimeConstant :=
  div_pos primeWeight_integral_pos (by norm_num)

theorem eventually_actualPrime_weight_large :
    ∀ᶠL:ℝ in atTop,∀p:ℕ→ℕ,∀n:ℕ,∀ _hzero:∀i,NeZero (p i),
      (∀i<n,(p i).Prime) → Set.InjOn p (Finset.range n:Set ℕ) →
      (∀i<n,p i≤ supplyPrimeCap L) →
      ∀S:∀i,Finset (ZMod (p i)),
      (∀i<n,(1/3:ℝ)≤density (S i)) → (∀i<n,density (S i)≤2/3) →
      (∀i<n,gamma (S i)≤ supplyEpsilon^2) → reciprocalMass (Finset.range n) p≤L →
      let X := (supplyRadius L)^2
      supplyPrimeConstant*kernelUnitProduct (Finset.range n) p S*(X:ℝ)/Real.log (X:ℝ) ≤
        ∑q∈primesInInterval (X/2) X,naturalKernelWeight p S n (supplyTruncation L) q := by
  have herror := Ostmann.ZeroDensity.eventually_totalPrimitivePrimeError_supply
    primeWeight_contDiff primeWeight_compact primeWeight_support
      (Real.log 1200+8*supplyEpsilon+10)
  filter_upwards [herror,eventually_supplyPrimeCap_le_radius,eventually_supply_tail_small,
    eventually_exp_tail_le_unit_multiple supplyPrimeConstant_pos,eventually_ge_atTop (1:ℝ)]
    with L herr hcap htail hsmall hL
  intro p n hzero hp hinj hbound S hlo hhi hg hH
  let : ∀i,NeZero (p i) := hzero
  let pf : Fin n→ℕ := fun i => p i
  let Sf : ∀i:Fin n,Finset (ZMod (pf i)) := fun i => S i
  let : ∀i:Fin n,Fact (pf i).Prime := fun i => ⟨hp i i.isLt⟩
  have hpf : Function.Injective pf := fun i j hij => Fin.ext (hinj
    (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt) hij)
  have hHf : (∑i:Fin n,(1:ℝ)/(pf i:ℝ))≤L := by
    simpa only [pf,reciprocalMass_fin_univ] using hH
  let X := (supplyRadius L)^2
  let K := supplyTruncation L
  let U := kernelUnitProduct (Finset.range n) p S
  let μ := unitWeightMean pf Sf K
  let J := ∫t in Ioi (0:ℝ),primeWeight t
  let W := naturalKernelWeight p S n K
  have hX : (0:ℝ)<X := by exact_mod_cast pow_pos (supplyRadius_pos L) 2
  have hJ : 0<J := primeWeight_integral_pos
  have hUexp := (kernelUnitProduct_exp_bounds (Finset.range n) p S
    (fun i hi => (hp i (Finset.mem_range.mp hi)).two_le)
    (fun i hi => hlo i (Finset.mem_range.mp hi))
    (fun i hi => hhi i (Finset.mem_range.mp hi))
    (fun i hi => hg i (Finset.mem_range.mp hi))).1
  have hU : 0<U := (Real.exp_pos _).trans_le hUexp
  have herrQ := herr (supplyCharacterCutoff L) (supplyCharacterCutoff_pos L) (supplyCharacterCutoff_le L)
  have hmean0 := actualPrimeMean_error hL hcap.1 hcap.2 pf hpf
    (fun i => hbound i i.isLt) Sf (fun i => hlo i i.isLt) (fun i => hhi i i.isLt)
    (fun i => hg i i.isLt) hHf
  have hW : (fun k => truncatedWeight Finset.univ
      (fun i:Fin n => localKernel (Sf i) sparseKernelScale (k:ZMod (pf i))) K)=W :=
    funext (fun k => naturalKernelWeight_fin_univ p S n K k)
  rw [hW] at hmean0
  have hmean : |weightedPrimeSum primeWeight (X:ℝ) W-μ*(X:ℝ)*J|≤(X:ℝ)*Real.exp (-10*L) := by
    apply hmean0.trans
    have h := mul_le_mul_of_nonneg_left herrQ
      (Real.exp_pos ((Real.log 1200+8*supplyEpsilon)*L)).le
    convert h using 1
    · rfl
    · rw [show -10*L=(Real.log 1200+8*supplyEpsilon)*L+
        (-(Real.log 1200+8*supplyEpsilon+10)*L) by ring,Real.exp_add]
      dsimp [X,Ostmann.ZeroDensity.supplyPrimeSample]
      ring
  have hμerr := unitWeightMean_error pf Sf K (fun i => hlo i i.isLt)
    (fun i => hhi i i.isLt) (fun i => hg i i.isLt)
  rw [unitKernelProduct_fin_univ p S n] at hμerr
  have ht := (htail _ (8*supplyEpsilon) hHf
    (by norm_num [supplyEpsilon]) (by norm_num [supplyEpsilon])).trans
      (supply_tail_le_half_unit hL hH hUexp)
  have hμlo : U/2≤μ := by
    have hm := (abs_le.mp (hμerr.trans ht)).1
    change -(U/2)≤μ-U at hm
    linarith
  have htailU := hsmall (reciprocalMass (Finset.range n) p) U hH hUexp
  have hlower : supplyPrimeConstant*U*(X:ℝ)≤weightedPrimeSum primeWeight (X:ℝ) W := by
    have he := (abs_le.mp hmean).1
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμlo hX.le) hJ.le
    have htX := mul_le_mul_of_nonneg_left htailU hX.le
    have hc : supplyPrimeConstant=J/4 := rfl
    rw [hc] at htX ⊢
    nlinarith
  have hupper := weightedPrimeSum_le_log_mul primeWeight W primeWeight_support
    primeWeight_nonneg primeWeight_le_one (naturalKernelWeight_nonneg p S n K) X
      (pow_pos (supplyRadius_pos L) 2)
  have hlogpos : 0<Real.log (X:ℝ) := (Real.exp_pos L).trans_le
    (Ostmann.ZeroDensity.log_supplyPrimeSample_lower L)
  exact (div_le_iff₀ hlogpos).mpr (by simpa only [mul_comm] using hlower.trans hupper)

end Ostmann.Supply

end

end OAI
