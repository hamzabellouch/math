import Mathlib
import OAI.Combinatorics.KMedian.Process.CountVariance
import OAI.Combinatorics.KMedian.Probability.BernoulliRealTransfer

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

def countSets (a : Fin (n+n*n)) : Finset (Fin n) :=
  (finSumFinEquiv.symm a).elim (fun i => {i})
    (fun ij => {(finProdFinEquiv.symm ij).1} ∪ {(finProdFinEquiv.symm ij).2})

def countCoefficients (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) (a : Fin (n+n*n)) : ℚ :=
  (finSumFinEquiv.symm a).elim b
    (fun ij => (1/2)*c (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2)

theorem countSets_card (a : Fin (n+n*n)) : (countSets a).card ≤ 2 := by
  unfold countSets
  cases finSumFinEquiv.symm a with
  | inl i => simp
  | inr ij => exact (card_union_le _ _).trans (by simp)

theorem count_polynomial (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) (q : Fin n → Bool) :
    polynomial countSets (countCoefficients b c) q=
      (∑ i,b i*flag q i)+(1/2)*∑ i, ∑ j, c i j*flag q i*flag q j := by
  unfold polynomial
  rw [← (finSumFinEquiv : Fin n ⊕ Fin (n*n) ≃ Fin (n+n*n)).sum_comp]
  simp only [countSets,countCoefficients,Equiv.symm_apply_apply,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,prod_singleton]
  congr 1
  rw [← (finProdFinEquiv : Fin n × Fin n ≃ Fin (n*n)).sum_comp]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,← product_union,prod_singleton,mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

@[simp] theorem cast_flag (q : Fin n → Bool) (i : Fin n) :
    (flag q i:ℝ)=CountStatistic.bit q i := by
  cases he : q i <;> simp [flag,CountStatistic.bit,he]

theorem cast_count_polynomial (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) (q : Fin n → Bool) :
    (polynomial countSets (countCoefficients b c) q:ℝ)=
      CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ)) q := by
  rw [count_polynomial]
  simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_one,
    Rat.cast_ofNat,cast_flag,CountStatistic.statistic]

theorem count_mean (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) :
    (run (d := 4) p hp n).real.expect
        (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ)))=
      (reference p hp).expect
        (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ))) := by
  have he := real_polynomial (d := 4) p hp countSets (countCoefficients b c)
    (fun a => (countSets_card a).trans (by omega))
  simpa only [cast_count_polynomial] using he

theorem count_variance (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) :
    (run (d := 4) p hp n).real.variance
        (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ)))=
      (reference p hp).variance
        (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ))) := by
  have he := quadratic_variance p hp countSets (countCoefficients b c) countSets_card
  simpa only [cast_count_polynomial] using he

theorem count_failure (p a m : Fin n → ℚ) (c : Fin n → Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {D P B t : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P) (ht : 0 < t)
    (hpP : ∀ i, (p i:ℝ) ≤ P) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, (a i:ℝ)+(m i:ℝ) ≤ B)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, (c i j:ℝ) ≤ (D-1)*(m i:ℝ))
    (hlinear : (∑ i, ((a i:ℝ)-(m i:ℝ))*(p i:ℝ)) ≤
      -t-(1/2)*P^2*(D-1)*∑ i, (m i:ℝ)) :
    (run (d := 4) p hp n).real.prob (fun q => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) q) ≤
      (P*D^2*B*(∑ i, ((a i:ℝ)+(m i:ℝ))))/t^2 := by
  let pR := fun i => (p i:ℝ)
  let aR := fun i => (a i:ℝ)
  let mR := fun i => (m i:ℝ)
  let cR := fun i j => (c i j:ℝ)
  have hp0 : ∀ i, 0 ≤ pR i := fun i => by dsimp only [pR]; exact_mod_cast (hp i).1
  have hp1 : ∀ i, pR i ≤ 1 := fun i => by dsimp only [pR]; exact_mod_cast (hp i).2
  have haR : ∀ i, 0 ≤ aR i := fun i => by dsimp only [aR]; exact_mod_cast ha i
  have hmR : ∀ i, 0 ≤ mR i := fun i => by dsimp only [mR]; exact_mod_cast hm i
  have hcR : ∀ i j, cR i j=cR j i := fun i j => congrArg (fun z : ℚ => (z:ℝ)) (hc i j)
  have hdR : ∀ i, cR i i=0 := fun i => by dsimp only [cR]; exact_mod_cast hdiag i
  have hc0R : ∀ i j, 0 ≤ cR i j := fun i j => by dsimp only [cR]; exact_mod_cast hc0 i j
  have hmean := CountStatistic.expectation_bound pR aR mR cR hp0 hp1 hP hD hpP hmR hdR hc0R hrow hlinear
  have hvar := CountStatistic.variance_bound pR aR mR cR hp0 hp1 hD hP hpP haR hmR hsize hcR hdR hc0R hrow
  have eqmean := count_mean p hp (fun i => a i-m i) c
  have eqvar := count_variance p hp (fun i => a i-m i) c
  simp only [Rat.cast_sub] at eqmean eqvar
  change _=(FiniteLaw.bernoulli pR hp0 hp1).expect _ at eqmean
  change _=(FiniteLaw.bernoulli pR hp0 hp1).variance _ at eqvar
  apply (FiniteLaw.prob_positive_le _ _ ht ?_).trans
    (div_le_div_of_nonneg_right (eqvar.le.trans hvar) (sq_nonneg t))
  rw [eqmean]
  linarith only [hmean]

end MetricKMedian.SparseBernoulli
end
end

end OAI
