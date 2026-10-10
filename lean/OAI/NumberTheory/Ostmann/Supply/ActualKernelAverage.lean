import OAI.NumberTheory.Ostmann.Supply.ActualKernelBudget
import OAI.NumberTheory.Ostmann.Supply.SupplyRadiusBounds
import OAI.NumberTheory.Ostmann.Supply.TruncationMargins

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter TensorModes TensorOperators Ostmann.Preliminaries
open scoped BigOperators

theorem eventually_supplyBand_primes_large :
    ∀ᶠL:ℝ in atTop, ∀p:ℕ,p.Prime → (1/20:ℝ)*L<Real.log (Real.log (p:ℝ)) → 1000≤p := by
  have hh : ∀ᶠL:ℝ in atTop,(1000:ℝ)≤Real.exp ((1/20:ℝ)*L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))).eventually
      (eventually_ge_atTop _)
  filter_upwards [hh] with L hL
  intro p hp hband
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have hl : 0<Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have h := Real.exp_lt_exp.mpr hband
  rw [Real.exp_log hl] at h
  exact_mod_cast hL.trans (h.le.trans (Real.log_le_self hp0.le))

theorem eventually_actualKernel_average_bound (d : Decomposition) :
    ∃ C:ℝ,0<C ∧ ∀ᶠL:ℝ in atTop, ∀p:ℕ→ℕ,∀n:ℕ,
      ∀ _hzero:∀i,NeZero (p i),
      (∀i<n,(p i).Prime) → Set.InjOn p (Finset.range n:Set ℕ) →
      (∀i<n,(1/20:ℝ)*L<Real.log (Real.log (p i:ℝ)) ∧
        Real.log (Real.log (p i:ℝ))≤(9/10:ℝ)*L) →
      (∀i<n,(1/3:ℝ)≤density (actualSupport d (p i))) →
      (∀i<n,density (actualSupport d (p i))≤2/3) →
      (∀i<n,gamma (actualSupport d (p i))≤ supplyEpsilon^2) →
      reciprocalMass (Finset.range n) p≤L →
      let A := upperWindow d.A ((supplyRadius L)^2)
      let B := upperWindow d.B ((supplyRadius L)^2)
      let S := fun i => actualSupport d (p i)
      kernelAverageWeight p S A B (fun a i => (a:ZMod (p i)))
        (fun b i => -(b:ZMod (p i))) n (supplyTruncation L) ≤
        3072*kernelUnitProduct (Finset.range n) p S*(supplyRadius L:ℝ)/
          Real.sqrt ((A.card:ℝ)*(B.card:ℝ))*
          Real.exp (-(8/5:ℝ)*reciprocalMass (Finset.range n) p+C*Real.sqrt L) := by
  obtain ⟨C,hC,hbudget⟩ := eventually_actualKernel_budgets d
  refine ⟨C,hC,?_⟩
  filter_upwards [hbudget,eventually_kernelTruncation_norm_contracted,
    eventually_supplyBand_primes_large,eventually_ge_atTop (1:ℝ)] with L hb hk hlarge hL
  intro p n hzero hp hinj hband hlo hhi hg hH
  let : ∀i,NeZero (p i) := hzero
  let A := upperWindow d.A ((supplyRadius L)^2)
  let B := upperWindow d.B ((supplyRadius L)^2)
  let S := fun i => actualSupport d (p i)
  obtain ⟨hAn,hBn,hA,hB,hba,hbb⟩ := hb p n hzero hp hinj hband
  have hp1000 := fun i hi => hlarge (p i) (hp i hi) (hband i hi).1
  have hnorm := hk p hzero S n hp1000 hlo hhi hg hH
  have hS : ∀i<n,(S i).Nonempty := by
    intro i hi
    simpa only [S,actualSupport_eq] using d.residueSupport_nonempty (p i)
  have hT : ∀i<n,(S i)ᶜ.Nonempty := by
    intro i hi
    simpa only [S,actualSupport_eq] using d.residueSupport_compl_nonempty (p i) (hp i hi)
  have hpair := kernelTruncation_lowMode_pairing p S A B
    (fun a i => (a:ZMod (p i))) (fun b i => -(b:ZMod (p i))) n (supplyTruncation L) hS hT hA hB
  have hexp : Real.exp (C*Real.sqrt (Real.log (Real.log (supplyRadius L:ℝ))))≤
      Real.exp (C*Real.sqrt L) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (supplyRadius_loglog_le hL)) hC.le)
  have hba' := hba.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hbb' := hbb.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hprod := product_le_common_budget (norm_nonneg _) (norm_nonneg _)
    (by positivity : 0≤1536*(supplyRadius L:ℝ)*Real.exp (C*Real.sqrt L))
    (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card)
    (by convert hba' using 1; ring) (by convert hbb' using 1; ring)
  have hnorm0 : 0≤2*kernelUnitProduct (Finset.range n) p S*
      Real.exp (-(8/5:ℝ)*reciprocalMass (Finset.range n) p) := (norm_nonneg _).trans hnorm
  calc
    _ ≤ ‖BivariateTruncation.rectangularTruncation (kernelTensorPolynomial p S n) (supplyTruncation L)‖*
        (‖lowModes (kernelCenteredCodomain p S) n (2*supplyTruncation L)
          (kernelOutputEmpirical p S A (fun a i => (a:ZMod (p i))) n)‖*
         ‖lowModes (kernelCenteredDomain p S) n (2*supplyTruncation L)
          (kernelInputEmpirical p S B (fun b i => -(b:ZMod (p i))) n)‖) := by
      simpa only [mul_assoc] using hpair
    _ ≤ (2*kernelUnitProduct (Finset.range n) p S*
      Real.exp (-(8/5:ℝ)*reciprocalMass (Finset.range n) p))*
      ((1536*(supplyRadius L:ℝ)*Real.exp (C*Real.sqrt L))/Real.sqrt ((A.card:ℝ)*(B.card:ℝ))) :=
        mul_le_mul hnorm hprod (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hnorm0
    _ = _ := by rw [Real.exp_add]; ring

end Ostmann.Supply

end

end OAI
