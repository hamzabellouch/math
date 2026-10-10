import OAI.NumberTheory.Ostmann.Supply.BoundaryCoverage
import OAI.NumberTheory.Ostmann.Supply.CoverageMargin
import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyPrimeScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Preliminaries
open scoped BigOperators

theorem eventually_actualPrime_weight_small (d : Decomposition) {η : ℝ} (hη : 0<η) :
    ∀ᶠL:ℝ in atTop, ∀p:ℕ→ℕ,∀n:ℕ,∀ _hzero:∀i,NeZero (p i),
      (∀i<n,(p i).Prime) → Set.InjOn p (Finset.range n:Set ℕ) →
      (∀i<n,(1/20:ℝ)*L<Real.log (Real.log (p i:ℝ)) ∧
        Real.log (Real.log (p i:ℝ))≤(9/10:ℝ)*L) →
      (∀i<n,(1/3:ℝ)≤density (actualSupport d (p i))) →
      (∀i<n,density (actualSupport d (p i))≤2/3) →
      (∀i<n,gamma (actualSupport d (p i))≤ supplyEpsilon^2) →
      (17/25:ℝ)*L≤reciprocalMass (Finset.range n) p →
      reciprocalMass (Finset.range n) p≤L →
      (n:ℝ)≤Real.exp (Real.exp ((9/10:ℝ)*L)) →
      let S := fun i => actualSupport d (p i)
      let X := (supplyRadius L)^2
      (∑q∈primesInInterval (X/2) X,naturalKernelWeight p S n (supplyTruncation L) q) ≤
        η*kernelUnitProduct (Finset.range n) p S*(X:ℝ)/Real.log (X:ℝ) := by
  obtain ⟨C,hC,hpair⟩ := eventually_actualKernel_pair_sum_bound d
  have hhalf : 0<η/2 := by positivity
  filter_upwards [hpair,eventually_pair_factor_small C hhalf,
    eventually_prime_coverage_upperWindows d (8*supplyEpsilon) hhalf,
    eventually_supplyBand_primes_large,eventually_ge_atTop (1:ℝ)] with L hpairs hmargin hcov hlarge hL
  intro p n hzero hp hinj hband hlo hhi hg hHlo hHhi hn
  let : ∀i,NeZero (p i) := hzero
  let S := fun i => actualSupport d (p i)
  let X := (supplyRadius L)^2
  let U := kernelUnitProduct (Finset.range n) p S
  have hUexp := (kernelUnitProduct_exp_bounds (Finset.range n) p S
    (fun i hi => (hp i (Finset.mem_range.mp hi)).two_le)
    (fun i hi => hlo i (Finset.mem_range.mp hi))
    (fun i hi => hhi i (Finset.mem_range.mp hi))
    (fun i hi => hg i (Finset.mem_range.mp hi))).1
  have hU : 0≤U := (Real.exp_pos _).le.trans hUexp
  have hUX : 0≤U*(X:ℝ) := mul_nonneg hU (Nat.cast_nonneg _)
  have hUlow : Real.exp (-(8*supplyEpsilon)*L)≤U := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hUexp
    have := mul_le_mul_of_nonneg_left hHhi (by norm_num [supplyEpsilon] : 0≤8*supplyEpsilon)
    linarith
  have hlog := Ostmann.ZeroDensity.log_supplyPrimeSample_bounds hL
  have hlogpos : 0<Real.log (X:ℝ) := (Real.exp_pos _).trans_le hlog.1
  have hfactor := hmargin (reciprocalMass (Finset.range n) p) (Real.log (X:ℝ)) hHlo hlogpos hlog.2
  have hb := hpairs p n hzero hp hinj hband hlo hhi hg hHhi
  have hsmall :
      (∑a∈upperWindow d.A X,∑b∈upperWindow d.B X,
        naturalKernelWeight p S n (supplyTruncation L) (a+b))≤(η/2)*U*(X:ℝ)/Real.log (X:ℝ) := by
    apply hb.trans
    have hm := mul_le_mul_of_nonneg_left hfactor hUX
    convert hm using 1 <;> dsimp [U,X] <;> push_cast <;> ring
  have hc := hcov p S n U hn hUlow
  change (∑q∈primesInInterval (X/2) X,naturalKernelWeight p S n (supplyTruncation L) q)≤
    η*U*(X:ℝ)/Real.log (X:ℝ)
  change (∑q∈primesInInterval (X/2) X,naturalKernelWeight p S n (supplyTruncation L) q)≤
    (∑a∈upperWindow d.A X,∑b∈upperWindow d.B X,
      naturalKernelWeight p S n (supplyTruncation L) (a+b))+(η/2)*U*(X:ℝ)/Real.log (X:ℝ) at hc
  apply hc.trans
  convert add_le_add_right hsmall ((η/2)*U*(X:ℝ)/Real.log (X:ℝ)) using 1 <;> ring

end Ostmann.Supply

end

end OAI
