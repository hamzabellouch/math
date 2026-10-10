import PrimeNumberTheoremAnd.Erdos970.MertensClassical
import OAI.NumberTheory.Jacobsthal.Analysis.PairDensityExpansion
import OAI.NumberTheory.Jacobsthal.Primes.WeightedChebyshev

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosRandomVariance

noncomputable def variancePrimes (w : ℝ) : Finset ℕ := (Finset.Ioc 0 ⌊w⌋₊).filter Nat.Prime

theorem variancePrimes_prime (w : ℝ) (p : ℕ) (hp : p ∈ variancePrimes w) : p.Prime :=
  (Finset.mem_filter.mp hp).2

theorem sieveProduct_pos (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) : 0 < sieveProduct P := by
  apply Finset.prod_pos
  intro p hp
  have h := hP p hp
  apply sub_pos.mpr
  exact (div_lt_one (show (0 : ℝ) < p by exact_mod_cast h.pos)).mpr
    (by exact_mod_cast h.one_lt)

theorem variance_product_limit :
    Tendsto (fun w : ℝ => Real.log w*sieveProduct (variancePrimes w)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have he3 : Tendsto _root_.Erdos970.Mertens.E₃ atTop (𝓝 (0 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp _root_.Erdos970.Mertens.E₃.bound'
  have h := he3.rexp.const_mul (Real.exp (-Real.eulerMascheroniConstant))
  simp only [Real.exp_zero,mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  rw [sieveProduct,variancePrimes,_root_.Erdos970.Mertens.prod_one_minus_div_prime_eq hw]
  field_simp [ne_of_gt (Real.log_pos hw)]

theorem source_mean_large (delta K : ℝ) (hdelta : 0 < delta) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, 1 < w ∧ ∀ J : ℕ, w^delta ≤ (J : ℝ) →
      K ≤ (J : ℝ)*sieveProduct (variancePrimes w) := by
  let c := Real.exp (-Real.eulerMascheroniConstant)/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlt : c < Real.exp (-Real.eulerMascheroniConstant) := by
    dsimp [c]; nlinarith [Real.exp_pos (-Real.eulerMascheroniConstant)]
  have hlow := variance_product_limit.eventually (lt_mem_nhds hlt)
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hdelta).bound (div_pos hc hK)
  filter_upwards [hlow,hsmall,eventually_gt_atTop (1 : ℝ)] with w hwc hlog hw
  refine ⟨hw,?_⟩
  intro J hJ
  have hw0 : 0 < w := by linarith
  have hL : 0 < Real.log w := Real.log_pos hw
  have hlog' : Real.log w ≤ (c/K)*w^delta := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hL,
      abs_of_nonneg (Real.rpow_nonneg hw0.le delta)] using hlog
  have hV : 0 < sieveProduct (variancePrimes w) := sieveProduct_pos _ (variancePrimes_prime w)
  have hm := mul_le_mul_of_nonneg_right hlog' hV.le
  have hbase : c/(c/K) ≤ w^delta*sieveProduct (variancePrimes w) := by
    apply (div_le_iff₀ (div_pos hc hK)).mpr
    nlinarith [hwc,hm]
  have he : c/(c/K)=K := by field_simp [hc.ne',hK.ne']
  rw [he] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_right hJ hV.le)

end ErdosRandomVariance

end


open _root_.Filter
namespace ErdosRandomVariance

universe u

theorem stable_prime_variance {α : Type*} (C : Finset α) (w : α → ℝ)
    (J : ℕ) (I : ℕ → α → ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (zeta : ℝ) (hzeta : 0 ≤ zeta)
    (hI : ∀ j ∈ Finset.range J, ∀ x ∈ C, I j x = 0 ∨ I j x = 1)
    (hMass : (∑ x ∈ C, w x) ≤ 1+zeta)
    (hLower : ∀ j ∈ Finset.range J, (1-zeta)*sieveProduct P ≤ weightedMoment C w (I j))
    (hUpper : ∀ j ∈ Finset.range J, weightedMoment C w (I j) ≤ (1+zeta)*sieveProduct P)
    (hPair : ∀ i ∈ Finset.range J, ∀ j ∈ Finset.range J, i ≠ j →
      weightedMoment C w (fun x => I i x*I j x) ≤ (1+zeta)*pairKernel P i j) :
    weightedMoment C w (fun x => (indicatorSum (Finset.range J) I x-(J : ℝ)*sieveProduct P)^2) ≤
      (1+zeta)*((J : ℝ)*sieveProduct P)+4*zeta*((J : ℝ)*sieveProduct P)^2 := by
  simpa only [Finset.card_range] using stable_finite_variance C w (Finset.range J) I
    (pairKernel P) (sieveProduct P) zeta (sieveProduct_pos P hP).le hzeta hI hMass hLower hUpper
    hPair (fun j _ => pairKernel_diagonal P j)
    (by simpa only [Finset.card_range] using pairKernel_interval_sum P hP J)

theorem stable_source_variance (delta eps : ℝ) (hdelta : 0 < delta) (heps : 0 < eps) :
    ∀ᶠ W : ℝ in atTop, 1 < W ∧ ∀ (J : ℕ), W^delta ≤ (J : ℝ) →
      ∀ (α : Type u) (C : Finset α) (w : α → ℝ) (I : ℕ → α → ℝ) (zeta : ℝ),
      0 ≤ zeta → zeta ≤ 1 →
      (∀ j ∈ Finset.range J, ∀ x ∈ C, I j x = 0 ∨ I j x = 1) →
      (∑ x ∈ C, w x) ≤ 1+zeta →
      (∀ j ∈ Finset.range J, (1-zeta)*sieveProduct (variancePrimes W) ≤ weightedMoment C w (I j)) →
      (∀ j ∈ Finset.range J, weightedMoment C w (I j) ≤ (1+zeta)*sieveProduct (variancePrimes W)) →
      (∀ i ∈ Finset.range J, ∀ j ∈ Finset.range J, i ≠ j →
        weightedMoment C w (fun x => I i x*I j x) ≤ (1+zeta)*pairKernel (variancePrimes W) i j) →
      weightedMoment C w
        (fun x => (indicatorSum (Finset.range J) I x-(J : ℝ)*sieveProduct (variancePrimes W))^2) ≤
        (eps+4*zeta)*((J : ℝ)*sieveProduct (variancePrimes W))^2 := by
  filter_upwards [source_mean_large delta (2/eps) hdelta (div_pos (by norm_num) heps)] with W hW
  refine ⟨hW.1,?_⟩
  intro J hJ α C w I zeta hzeta hzeta1 hI hMass hLower hUpper hPair
  let M := (J : ℝ)*sieveProduct (variancePrimes W)
  have hM : 2/eps ≤ M := hW.2 J hJ
  have hM0 : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) (sieveProduct_pos _ (variancePrimes_prime W)).le
  have h2 : 2 ≤ eps*M := by nlinarith [(div_le_iff₀ heps).mp hM]
  have hmain := stable_prime_variance C w J I (variancePrimes W) (variancePrimes_prime W)
    zeta hzeta hI hMass hLower hUpper hPair
  change weightedMoment C w (fun x => (indicatorSum (Finset.range J) I x-M)^2) ≤ (eps+4*zeta)*M^2
  change weightedMoment C w (fun x => (indicatorSum (Finset.range J) I x-M)^2) ≤ (1+zeta)*M+4*zeta*M^2 at hmain
  nlinarith [mul_le_mul_of_nonneg_right h2 hM0,mul_le_mul_of_nonneg_right hzeta1 hM0]

end ErdosRandomVariance


end Erdos970

end OAI
