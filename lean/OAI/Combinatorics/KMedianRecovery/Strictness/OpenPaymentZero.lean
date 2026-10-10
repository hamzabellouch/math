import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.ClippedBid
import OAI.Combinatorics.KMedianRecovery.Strictness.BaselineDual

namespace OAI

namespace MetricKMedianRecovery.PriceTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

lemma open_payment_zero (loc : D → X) (Q : Finset X) (t K v z : ℝ) (i : X)
    (hi : i ∈ Q) (ht : 0 ≤ t) (tau : D → ℝ)
    (hb : admissibleBids loc t K v z Q i tau) :
    openingPayment loc t z Q i tau = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : activeAt loc t z Q j
  · simp only [hj,↓reduceIte]
    apply max_eq_right
    have hh := (hb j hj).2.2.1 i hi
    rw [dist_comm (loc j) i] at hh
    linarith only [hh]
  · simp only [hj,↓reduceIte]
    apply max_eq_right
    have hh := mul_le_mul_of_nonneg_left (nearestDistance_le_mem (loc j) Q i hi) ht
    rw [dist_comm (loc j) i] at hh
    linarith only [hh]

theorem maximal_payment_lt (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (hmax : ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i)
    (i : X) (hi : i ∈ F) (tau : D → ℝ)
    (hadm : admissibleBids loc (1-3*v) (1+v^2) v z Q i tau) :
    openingPayment loc (1-3*v) z Q i tau < lam := by
  by_contra hn
  obtain ⟨k,hk,hopen⟩ := payment_produces_openable loc F Q v z lam
    hv hvsmall hz hlam hbase i hi tau hadm (le_of_not_gt hn)
  by_cases hkQ : k ∈ Q
  · obtain ⟨b,hb,hp,_⟩ := hopen
    have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
    have he := open_payment_zero loc Q (1-3*v) (1+v^2) v z k hkQ ht b hb
    simp only [mul_zero,sub_zero,he] at hp
    exact (not_le_of_gt hlam) hp
  · exact hmax k hk hkQ hopen

theorem maximal_price_mono (loc : D → X) (F Q : Finset X) (v z lam lam' : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (hmax : ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i)
    (hm : lam ≤ lam') :
    ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam' 0 i := by
  intro i hi _ hop
  obtain ⟨tau,hb,hp,_⟩ := hop
  have hh := maximal_payment_lt loc F Q v z lam hv hvsmall hz hlam hbase hmax i hi tau hb
  simp only [mul_zero,sub_zero] at hp
  exact (not_lt_of_ge (hm.trans hp)) hh

theorem lift_payment (loc : D → X) (Q Q' : Finset X) (t K v z : ℝ)
    (hQ : Q.Nonempty) (hQ' : Q'.Nonempty) (ht : 0 ≤ t) (hK : z ≤ K*z)
    (hr : ∀ j, nearestDistance (loc j) Q' ≤ nearestDistance (loc j) Q)
    (i : X) (tau : D → ℝ) (hb : admissibleBids loc t K v z Q' i tau) :
    ∃ tauOld : D → ℝ, admissibleBids loc t K v z Q i tauOld ∧
      openingPayment loc t z Q' i tau ≤ openingPayment loc t z Q i tauOld := by
  classical
  let tauOld : D → ℝ := fun j => if activeAt loc t z Q' j then tau j else z
  have hadm : admissibleBids loc t K v z Q i tauOld := by
    intro j hj
    by_cases hj' : activeAt loc t z Q' j
    · simp only [tauOld,ite_eq_left hj']
      refine ⟨(hb j hj').1,(hb j hj').2.1,?_,(hb j hj').2.2.2⟩
      intro f hf
      exact ((ClippingTransfer.bid_cap loc t K v z Q' hQ' i tau hb j hj').trans
        (mul_le_mul_of_nonneg_left (hr j) ht)).trans
        (mul_le_mul_of_nonneg_left (nearestDistance_le_mem (loc j) Q f hf) ht)
    · simp only [tauOld,ite_eq_right hj']
      exact ⟨le_rfl,hK,fun f hf => (hj f hf).le,fun _ => trivial⟩
  refine ⟨tauOld,hadm,?_⟩
  apply Finset.sum_le_sum
  intro j _
  by_cases hj' : activeAt loc t z Q' j
  · have hj := ClippingTransfer.active_transfer loc t z Q Q' hQ hQ' ht hr j hj'
    simp only [hj',hj,↓reduceIte,tauOld]
    exact le_rfl
  · by_cases hj : activeAt loc t z Q j
    · simp only [hj',hj,↓reduceIte,tauOld]
      apply max_le_max _ le_rfl
      apply sub_le_sub_right
      exact not_lt.mp (fun hh => hj' ((activeAt_iff loc t z Q' j ht hQ').mpr hh))
    · simp only [hj',hj,↓reduceIte]
      exact max_le_max (sub_le_sub_right (mul_le_mul_of_nonneg_left (hr j) ht) _) le_rfl

theorem maximal_shrink (loc : D → X) (F Q Q' : Finset X) (v z lam lam' : ℝ)
    (hQ : Q.Nonempty) (hQ' : Q'.Nonempty)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (hmax : ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i)
    (hm : lam ≤ lam') (hr : ∀ j, nearestDistance (loc j) Q' ≤ nearestDistance (loc j) Q) :
    ∀ i ∈ F, i ∉ Q' → ¬etaOpenable loc F Q' (1-3*v) (1+v^2) v z lam' 0 i := by
  intro i hi _ hop
  obtain ⟨tau,hb,hp,_⟩ := hop
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hK : z ≤ (1+v^2)*z := by nlinarith only [mul_nonneg (sq_nonneg v) hz.le]
  obtain ⟨old,hadm,hpay⟩ := lift_payment loc Q Q' (1-3*v) (1+v^2) v z hQ hQ' ht hK hr i tau hb
  have hh := maximal_payment_lt loc F Q v z lam hv hvsmall hz hlam hbase hmax i hi old hadm
  simp only [mul_zero,sub_zero] at hp
  exact (not_lt_of_ge ((hm.trans hp).trans hpay)) hh
end MetricKMedianRecovery.PriceTransfer

end OAI
