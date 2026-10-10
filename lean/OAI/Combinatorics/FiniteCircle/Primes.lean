import OAI.Combinatorics.FiniteCircle.ExcludedDescent

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

def primeInterval (n : ℕ) : Finset ℕ := (Finset.Ioc n (2*n)).filter Nat.Prime

theorem centralBinom_le_interval (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^Nat.sqrt (2*n) * 4^(2*n/3) * ∏ p ∈ primeInterval n, p := by
  classical
  let f : ℕ → ℕ := fun p => p^n.centralBinom.factorization p
  have hsmall : (∏ p ∈ Finset.range (2*n/3+1), f p) ≤ (2*n)^Nat.sqrt (2*n)*4^(2*n/3) := by
    let S := (Finset.range (2*n/3+1)).filter Nat.Prime
    have he : (∏ p ∈ S, f p) = ∏ p ∈ Finset.range (2*n/3+1), f p := by
      apply Finset.prod_filter_of_ne
      intro p _ hp
      contrapose hp
      simp only [f, Nat.factorization_eq_zero_of_not_prime n.centralBinom hp, pow_zero]
    rw [← he, ← Finset.prod_filter_mul_prod_filter_not S (fun p => p ≤ Nat.sqrt (2*n))]
    apply Nat.mul_le_mul
    · calc
        _ ≤ ∏ _p ∈ S.filter (fun p => p ≤ Nat.sqrt (2*n)), 2*n :=
          Finset.prod_le_prod (fun p _ => Nat.pow_factorization_choose_le (by omega : 0<2*n))
        _ = (2*n)^(S.filter (fun p => p ≤ Nat.sqrt (2*n))).card := by simp
        _ ≤ _ := by
          apply Nat.pow_le_pow_right (by omega)
          have hs : S.filter (fun p => p ≤ Nat.sqrt (2*n)) ⊆ Finset.Icc 1 (Nat.sqrt (2*n)) := by
            intro p hp
            obtain ⟨hp,hq⟩ := Finset.mem_filter.mp hp
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.one_lt.le,hq⟩
          have hh := Finset.card_le_card hs
          simpa using hh
    · calc
        _ ≤ ∏ p ∈ S.filter (fun p => ¬p ≤ Nat.sqrt (2*n)), p := by
          apply Finset.prod_le_prod
          intro p hp
          obtain ⟨hp,hq⟩ := Finset.mem_filter.mp hp
          dsimp [f]
          have hfac : n.centralBinom.factorization p ≤ 1 :=
            Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (lt_of_not_ge hq))
          exact (Nat.pow_le_pow_right (Finset.mem_filter.mp hp).2.one_lt.le hfac).trans_eq (pow_one p)
        _ ≤ primorial (2*n/3) := by
          apply Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
          intro p hp _
          exact (Finset.mem_filter.mp hp).2.one_lt.le
        _ ≤ _ := primorial_le_four_pow _
  have htail : (∏ p ∈ Finset.Ico (2*n/3+1) (2*n+1), f p) ≤ ∏ p ∈ primeInterval n, p := by
    have hs : primeInterval n ⊆ Finset.Ico (2*n/3+1) (2*n+1) := by
      intro p hp
      have h := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
      have hdiv : 2*n/3 ≤ n := (Nat.div_le_iff_le_mul_add_pred (by decide : 0<3)).mpr (by omega)
      exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
    have he : (∏ p ∈ primeInterval n, f p) = ∏ p ∈ Finset.Ico (2*n/3+1) (2*n+1), f p := by
      apply Finset.prod_subset hs
      intro p hp hnot
      dsimp [f]
      by_cases hprime : p.Prime
      · have hp' := Finset.mem_Ico.mp hp
        have hpn : p ≤ n := by
          by_contra h
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,hprime⟩)
        rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn (by omega), pow_zero]
      · rw [Nat.factorization_eq_zero_of_not_prime _ hprime, pow_zero]
    rw [← he]
    apply Finset.prod_le_prod
    intro p hp
    obtain ⟨hpi,hp⟩ := Finset.mem_filter.mp hp
    have hpn := (Finset.mem_Ioc.mp hpi).1
    have hfac : n.centralBinom.factorization p ≤ 1 := Nat.factorization_choose_le_one (by nlinarith)
    exact (Nat.pow_le_pow_right hp.one_lt.le hfac).trans_eq (pow_one p)
  calc
    _ = (∏ p ∈ Finset.range (2*n/3+1), f p) * ∏ p ∈ Finset.Ico (2*n/3+1) (2*n+1), f p := by
      rw [Finset.prod_range_mul_prod_Ico _ (by omega)]
      exact (Nat.prod_pow_factorization_centralBinom n).symm
    _ ≤ _ := Nat.mul_le_mul hsmall htail

 theorem centralBinom_le_interval_card (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^Nat.sqrt (2*n) * 4^(2*n/3) * (2*n)^(primeInterval n).card := by
  refine (centralBinom_le_interval n hn).trans (Nat.mul_le_mul_left _ ?_)
  calc
    _ ≤ ∏ _p ∈ primeInterval n, 2*n := Finset.prod_le_prod (fun p hp =>
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2)
    _ = _ := by simp

theorem log_le_linear_million {x : ℝ} (hx : 1000000 ≤ x) :
    Real.log x ≤ x / 500 := by
  have hp : 0 < x := by linarith
  have hs : Real.sqrt x ≤ x/1000 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have h := mul_nonneg (show 0 ≤ x-1000000 by linarith) hp.le
      nlinarith
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hp)
  rw [Real.log_sqrt hp.le] at hl
  linarith

theorem primeInterval_card_cubic (h : ℕ) (hh : 1000000 ≤ h) :
    h^2 ≤ (primeInterval (h^3)).card := by
  have htwo : 2 ≤ h := by omega
  have hN : 4 ≤ h^3 := by nlinarith [Nat.pow_le_pow_left htwo 3]
  have hH : (1000000:ℝ) ≤ h := by exact_mod_cast hh
  have hp : (0:ℝ) < h := by positivity
  have hhlog := log_le_linear_million hH
  have hlog0 : 0 ≤ Real.log (h:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ h by omega))
  have hlog4 : (3:ℝ)/4 ≤ Real.log 4 := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(4:ℝ)⁻¹)
    rw [Real.log_inv] at hl
    norm_num at hl ⊢
    linarith
  have hsqrt : Nat.sqrt (2*h^3) ≤ 2*h^2 := by
    have he : 2*h^3 ≤ (2*h^2)^2 := by nlinarith [sq_nonneg (h:ℤ), Nat.pow_le_pow_left htwo 2]
    exact (Nat.sqrt_le_sqrt he).trans_eq (Nat.sqrt_eq' _)
  by_contra hn
  have hc : (primeInterval (h^3)).card ≤ h^2 := by omega
  have hbin := centralBinom_le_interval_card (h^3) (by omega)
  have hpow : 4^(h^3) < h^3 * ((2*h^3)^(3*h^2) * 4^(2*h^3/3)) := by
    apply (Nat.four_pow_lt_mul_centralBinom (h^3) hN).trans_le
    apply Nat.mul_le_mul_left
    apply hbin.trans
    calc
      _ = (2*h^3)^(Nat.sqrt (2*h^3)+(primeInterval (h^3)).card)*4^(2*h^3/3) := by
        rw [pow_add]
        ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hpowR : (4:ℝ)^(h^3) < (h:ℝ)^3 *((2*(h:ℝ)^3)^(3*h^2)*4^(2*h^3/3)) := by
    exact_mod_cast hpow
  have hlog := (Real.log_lt_log (by positivity) hpowR)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at hlog
  simp only [Real.log_pow] at hlog
  have hlog2 : Real.log (2*(h:ℝ)^3) ≤ 4*Real.log (h:ℝ) := by
    have ht : 2*(h:ℝ)^3 ≤ (h:ℝ)^4 := by
      have hh2 : (2:ℝ) ≤ h := by exact_mod_cast htwo
      nlinarith [mul_nonneg (show 0 ≤ (h:ℝ)-2 by linarith) (show 0 ≤ (h:ℝ)^3 by positivity)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity) ht
  have hdiv : ((2*h^3/3:ℕ):ℝ) ≤ 2*(h:ℝ)^3/3 := by
    exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := 2*h^3) (n := 3))
  have hmul := mul_le_mul_of_nonneg_right hdiv (show 0 ≤ Real.log 4 by linarith)
  have hmul2 := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ) ≤ (3*h^2:ℕ) by positivity)
  have hbound : (h:ℝ)^3*Real.log 4/3 < (3+12*(h:ℝ)^2)*Real.log h := by
    push_cast at hlog hmul2
    nlinarith
  have hlarge : (3+12*(h:ℝ)^2)*Real.log h ≤ 13*(h:ℝ)^2*((h:ℝ)/500) := by
    have hh2 : (2:ℝ) ≤ h := by exact_mod_cast htwo
    have ha : 3+12*(h:ℝ)^2 ≤ 13*(h:ℝ)^2 := by nlinarith
    exact mul_le_mul ha hhlog hlog0 (by positivity)
  have hlower := mul_le_mul_of_nonneg_left hlog4 (show 0 ≤ (h:ℝ)^3/3 by positivity)
  have hcube : 0 < (h:ℝ)^3 := by positivity
  nlinarith

theorem prime_array (h : ℕ) (hh : 1000000 ≤ h) :
    ∃ p : ℕ → ℕ → ℕ,
      (∀ l k : Fin h, Nat.Prime (p (l.val+1) k) ∧ h^3 < p (l.val+1) k ∧ p (l.val+1) k ≤ 2*h^3) ∧
      Function.Injective (fun lk : Fin h × Fin h => p (lk.1.val+1) lk.2) ∧
      (∀ l k, ¬(1 ≤ l ∧ l ≤ h ∧ k < h) → p l k = 1) := by
  classical
  obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq (primeInterval_card_cubic h hh)
  let e : (Fin h × Fin h) ≃ s := Fintype.equivOfCardEq (by simp [hcard, pow_two])
  let p : ℕ → ℕ → ℕ := fun l k => if hl : 1 ≤ l ∧ l ≤ h then
    if hk : k < h then (e (⟨l-1,by omega⟩,⟨k,hk⟩)).val else 1 else 1
  have hep (l k : Fin h) : p (l.val+1) k = (e (l,k)).val := by
    simp only [p, show 1 ≤ l.val+1 ∧ l.val+1 ≤ h by omega, dite_true, k.isLt]
    rfl
  refine ⟨p, ?_, ?_, ?_⟩
  · intro l k
    rw [hep]
    have he := hs (e (l,k)).property
    obtain ⟨he,hprime⟩ := Finset.mem_filter.mp he
    have hv := Finset.mem_Ioc.mp he
    exact ⟨hprime,hv.1,hv.2⟩
  · intro x y he
    simp only [hep] at he
    exact e.injective (Subtype.ext he)
  · intro l k hn
    dsimp [p]
    split_ifs with hl hk
    · exact False.elim (hn ⟨hl.1,hl.2,hk⟩)
    · rfl
    · rfl

structure StandingPrimes (h : ℕ) (p : ℕ → ℕ → ℕ) : Prop where
  inside : ∀ l k : Fin h, Nat.Prime (p (l.val+1) k) ∧ h^3 < p (l.val+1) k ∧ p (l.val+1) k ≤ 2*h^3
  inj : Function.Injective (fun lk : Fin h × Fin h => p (lk.1.val+1) lk.2)
  outside : ∀ l k, ¬(1 ≤ l ∧ l ≤ h ∧ k < h) → p l k = 1

 theorem standingPrimes_exists (h : ℕ) (hh : 1000000 ≤ h) :
    ∃ p, StandingPrimes h p := by
  obtain ⟨p,hp,hi,ho⟩ := prime_array h hh
  exact ⟨p,⟨hp,hi,ho⟩⟩

namespace StandingPrimes
variable {h : ℕ} {p : ℕ → ℕ → ℕ} (hp : StandingPrimes h p)
include hp

 theorem atLevel (l : ℕ) (hl : 1 ≤ l) (hlh : l ≤ h) (k : Fin h) :
    Nat.Prime (p l k) ∧ h^3 < p l k ∧ p l k ≤ 2*h^3 := by
  have ht := hp.inside ⟨l-1,by omega⟩ k
  simpa only [show l-1+1=l by omega] using ht

 theorem positive (l : ℕ) (k : Fin h) : 0 < p l k := by
  by_cases hl : 1 ≤ l ∧ l ≤ h
  · exact (hp.atLevel l hl.1 hl.2 k).1.pos
  · rw [hp.outside l k (by omega)]
    norm_num

 theorem level_injective (l : ℕ) (hl : 1 ≤ l) (hlh : l ≤ h) :
    Function.Injective (fun k : Fin h => p l k) := by
  intro i j he
  have hi := hp.inj (a₁ := (⟨l-1,by omega⟩,i)) (a₂ := (⟨l-1,by omega⟩,j))
    (by simpa only [show l-1+1=l by omega] using he)
  exact congrArg Prod.snd hi

 theorem level_distinct (l r : ℕ) (hl : 1 ≤ l) (hlh : l ≤ h)
    (hr : 1 ≤ r) (hrh : r ≤ h) (hlr : l ≠ r) (i j : Fin h) : p l i ≠ p r j := by
  intro he
  have hi := hp.inj (a₁ := (⟨l-1,by omega⟩,i)) (a₂ := (⟨r-1,by omega⟩,j))
    (by simpa only [show l-1+1=l by omega, show r-1+1=r by omega] using he)
  have hh := congrArg (fun z : Fin h × Fin h => z.1.val) hi
  apply hlr
  dsimp only at hh
  omega

 theorem coprime (l : ℕ) : Pairwise (fun i j : Fin h => Nat.Coprime (p l i) (p l j)) := by
  intro i j hij
  by_cases hl : 1 ≤ l ∧ l ≤ h
  · exact ((hp.atLevel l hl.1 hl.2 i).1.coprime_iff_not_dvd).mpr (by
      intro hd
      have he := ((hp.atLevel l hl.1 hl.2 j).1.dvd_iff_eq (hp.atLevel l hl.1 hl.2 i).1.ne_one).mp hd
      exact hij (hp.level_injective l hl.1 hl.2 he.symm))
  · rw [hp.outside l i (by omega), hp.outside l j (by omega)]
    exact Nat.coprime_one_left _

 theorem period_pos (l : ℕ) : 0 < period h p l :=
  Finset.prod_pos (fun k _ => hp.positive l k)

 theorem circle_pos : 0 < circleSize h p := by
  apply Nat.mul_pos (by norm_num)
  exact Finset.prod_pos (fun l _ => hp.period_pos (l.val+1))

 omit hp in
 theorem circle_even : circleSize h p = 2*(circleSize h p/2) := by
  unfold circleSize
  omega

 theorem divides_circle (l : ℕ) (k : Fin h) : p l k ∣ circleSize h p := by
  by_cases hl : 1 ≤ l ∧ l ≤ h
  · have hk : p l k ∣ period h p l := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
    have hd : period h p l ∣ ∏ r : Fin h, period h p (r.val+1) := by
      have hh := Finset.dvd_prod_of_mem (fun r : Fin h => period h p (r.val+1))
        (Finset.mem_univ (⟨l-1,by omega⟩ : Fin h))
      simpa only [show l-1+1=l by omega] using hh
    exact hk.trans (hd.trans (dvd_mul_left _ _))
  · rw [hp.outside l k (by omega)]
    exact one_dvd _

 theorem maskPrimes : MaskPrimes h p := by
  exact ⟨fun l k => (hp.inside l k).1, hp.inj, fun l k => ⟨(hp.inside l k).2.1.le,(hp.inside l k).2.2⟩⟩

 theorem excludedPrimes (hh : 2 ≤ h) : ExcludedPrimes h p := by
  refine ⟨fun l k => (hp.inside l k).1, hp.inj, fun l k => ⟨(hp.inside l k).2.1, ?_⟩⟩
  apply (hp.inside l k).2.2.trans
  have hh2 : 2 ≤ h^2 := by nlinarith
  calc
    2*h^3 ≤ h^2*h^3 := Nat.mul_le_mul_right _ hh2
    _ = h^5 := by ring

end StandingPrimes

end FiniteCircle

end OAI
