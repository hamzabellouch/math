import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Entry
import OAI.Combinatorics.KMedianRecovery.Strictness.OpenPaymentZero

namespace OAI

namespace MetricKMedianRecovery.MaximalPrefixSelection
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [DecidableEq X] in

theorem maximal_superset (loc : D → X) (F Q Q' : Finset X) (v z lam lam' : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (hmax : PhaseSequence.Maximal loc F Q v z lam)
    (hprice : lam ≤ lam') (hQQ : Q ⊆ Q') :
    PhaseSequence.Maximal loc F Q' v z lam' := by
  classical
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hK : z ≤ (1+v^2)*z := by nlinarith only [mul_nonneg (sq_nonneg v) hz.le]
  by_cases hQ : Q.Nonempty
  · exact PriceTransfer.maximal_shrink loc F Q Q' v z lam lam' hQ (hQ.mono hQQ)
      hv hvsmall hz hlam hbase hmax hprice (fun j => nearestDistance_antitone (loc j) Q Q' hQ hQQ)
  have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
  subst Q
  intro i hi _ hop
  obtain ⟨tau,hb,hp,_⟩ := hop
  have hactive (j : D) : activeAt loc (1-3*v) z ∅ j := by simp [activeAt]
  let old : D → ℝ := fun j => if activeAt loc (1-3*v) z Q' j then tau j else z
  have hadm : admissibleBids loc (1-3*v) (1+v^2) v z ∅ i old := by
    intro j _
    by_cases hj : activeAt loc (1-3*v) z Q' j
    · simp only [old,ite_eq_left hj]
      exact ⟨(hb j hj).1,(hb j hj).2.1,by simp,(hb j hj).2.2.2⟩
    · simp only [old,ite_eq_right hj]
      exact ⟨le_rfl,hK,by simp,fun _ => trivial⟩
  have hpay : openingPayment loc (1-3*v) z Q' i tau ≤
      openingPayment loc (1-3*v) z ∅ i old := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : activeAt loc (1-3*v) z Q' j
    · simp only [hj,hactive j,↓reduceIte,old]
      exact le_rfl
    · have hn : Q'.Nonempty := inactive_nonempty loc (1-3*v) z Q' j hj
      have hz' : (1-3*v)*nearestDistance (loc j) Q' ≤ z := by
        exact not_lt.mp (fun hh => hj ((activeAt_iff loc (1-3*v) z Q' j ht hn).mpr hh))
      simp only [hj,hactive j,↓reduceIte,old]
      exact max_le_max (sub_le_sub_right hz' _) le_rfl
  have hlt := PriceTransfer.maximal_payment_lt loc F ∅ v z lam hv hvsmall hz hlam
    hbase hmax i hi old hadm
  simp only [mul_zero,sub_zero] at hp
  exact (not_lt_of_ge ((hprice.trans hp).trans hpay)) hlt

end MetricKMedianRecovery.MaximalPrefixSelection

end OAI
