import OAI.Combinatorics.FiniteCircle.Primes

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem halfturn_ne_zero {M : ℕ} [NeZero M] (he : M=2*(M/2)) :
    ((M/2:ℕ) : ZMod M) ≠ 0 := by
  intro hz
  have hd := (CharP.cast_eq_zero_iff (ZMod M) M (M/2)).mp hz
  have hm := NeZero.pos M
  have hh : 0 < M/2 := by omega
  have hw := Nat.le_of_dvd hh hd
  omega

 theorem halfturn_supported {M : ℕ} (he : M=2*(M/2)) :
    PhaseSupported {2} ((M/2:ℕ) : ZMod M) := by
  simp only [PhaseSupported, Finset.prod_singleton, nsmul_eq_mul]
  rw [← Nat.cast_mul, ← he]
  simp

 theorem StandingPrimes.mask_tags_ge {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 4 ≤ h) (l : ℕ) : 4 ≤ (maskTags h p l).length := by
  rw [length_maskTags]
  calc
    4 ≤ h := hh
    _ = ∑ _k : Fin h, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun k _ => hp.positive l k)

 theorem StandingPrimes.half_fresh {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : l ≤ h) : LowerFresh h p l {2} := by
  intro j hj hjl k hk
  have ht := (hp.atLevel j hj (hjl.trans hl) k).2.1
  have hh3 := Nat.pow_le_pow_left hh 3
  simp only [Finset.mem_singleton] at hk
  omega

 theorem mask_long_deficit {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2))
    {p : ℕ → ℕ → ℕ} (hp : StandingPrimes (n^4) p) {R : ℕ} (hR : 0<R)
    (v : MaskState (n^4) p (circleSize (n^4) p) (n^4)) :
    (maskLength (n^4) p R (circleSize (n^4) p) (n^4):ℝ)/(n:ℝ)^(3*n^4) ≤
      (deficit (maskWord (n^4) p R (circleSize (n^4) p) (n^4) v)
        (maskWord (n^4) p R (circleSize (n^4) p) (n^4)
          (shiftMaskState (n^4) p (circleSize (n^4) p) (n^4) v ((circleSize (n^4) p/2 : ℕ) : ZMod (circleSize (n^4) p)))) : ℝ) := by
  let h := n^4
  let M := circleSize h p
  let : NeZero M := ⟨hp.circle_pos.ne'⟩
  have hh : 1000000 ≤ h := hn.trans (le_self_pow₀ (by omega) (by norm_num))
  have ht : 2 ≤ n^2 := by nlinarith
  have hht : h ≤ (n^2)^2 := by dsimp [h]; ring_nf; rfl
  have hth : 2*n^2 ≤ h := by dsimp [h]; nlinarith
  have hK : 2 ≤ h/100 := by omega
  have hbound := mask_denominator_descent ht hht hth hK hp.divides_circle hp.positive
    (fun j hj hjh k => (hp.atLevel j hj hjh k).1)
    (fun j hj hjh k => (hp.atLevel j hj hjh k).2.1.le)
    (fun j hj hjh k => (hp.atLevel j hj hjh k).2.2) hp.level_distinct
    h (le_refl _) {2} ((M/2:ℕ) : ZMod M) (by simp; omega)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; subst q
        exact ⟨Nat.prime_two, (show 2≤h by omega).trans (le_self_pow₀ (by omega) (by norm_num))⟩)
    (hp.half_fresh (by omega) h (le_refl _))
    (halfturn_ne_zero (StandingPrimes.circle_even (h:=h) (p:=p)))
    (halfturn_supported (StandingPrimes.circle_even (h:=h) (p:=p)))
  simp only [Finset.card_singleton] at hbound
  have hsep := mask_separation (StandingPrimes.circle_even (h:=h) (p:=p)) (by omega : 0<h)
    hR hp.divides_circle hp.positive (hp.mask_tags_ge (by omega)) h v ((M/2:ℕ) : ZMod M)
  have hnum := mask_descent_numeric hn he
  have hL : (0:ℝ) ≤ maskLength h p R M h := by positivity
  have hc : (0:ℝ) ≤ 1/((2:ℝ)^h*4) := by positivity
  calc
    _ = (maskLength h p R M h:ℝ)*(1/(n:ℝ)^(3*h)) := by dsimp [h,M]; ring
    _ ≤ (maskLength h p R M h:ℝ)*((1/((2:ℝ)^h*4))*descentBound h (h/100) (n^2) 1 h) :=
      mul_le_mul_of_nonneg_left hnum hL
    _ ≤ (1/((2:ℝ)^h*4))*(maskLength h p R M h)*maskCost h p M hp.divides_circle hp.positive h ((M/2:ℕ) : ZMod M) := by
      nlinarith [mul_le_mul_of_nonneg_left hbound (mul_nonneg hL hc)]
    _ ≤ _ := hsep

 theorem excluded_long_deficit {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2))
    {p : ℕ → ℕ → ℕ} (hp : StandingPrimes (n^4) p) {R : ℕ} (hR : 0<R)
    (v : ExcludedState (n^4) (circleSize (n^4) p) (n^4)) :
    (excludedLength (n^4) p R (circleSize (n^4) p) (n^4):ℝ)/(n:ℝ)^(3*n^4) ≤
      (deficit (excludedWord (n^4) p R (circleSize (n^4) p) (n^4) v)
        (excludedWord (n^4) p R (circleSize (n^4) p) (n^4)
          (shiftExcludedState (n^4) (circleSize (n^4) p) (n^4) v ((circleSize (n^4) p/2 : ℕ) : ZMod (circleSize (n^4) p)))) : ℝ) := by
  let h := n^4
  let M := circleSize h p
  let : NeZero M := ⟨hp.circle_pos.ne'⟩
  have hh : 1000000 ≤ h := hn.trans (le_self_pow₀ (by omega) (by norm_num))
  have ht : 2 ≤ n^3 := by nlinarith [Nat.pow_le_pow_left (show 2≤n by omega) 3]
  have htt : h ≤ n^3*n := by dsimp [h]; ring_nf; rfl
  have hsmall : 2*n^3 ≤ h := by
    have ht := Nat.mul_le_mul_right (n^3) (show 2≤n by omega)
    dsimp [h]; nlinarith [show n*n^3=n^4 by ring]
  have hbound := excluded_denominator_descent ht (by omega : 1≤n) (le_refl (n^4)) htt hsmall
    (by omega : 3≤h/100) hp.divides_circle hp.positive
    (fun j hj hjh k => (hp.atLevel j hj hjh k).1)
    (fun j hj hjh k => by
      have ht := ((hp.excludedPrimes (by omega)).2.2 ⟨j-1,by omega⟩ k).2
      simpa only [show j-1+1=j by omega] using ht) hp.level_injective hp.level_distinct
    h (le_refl _) {2} ((M/2:ℕ) : ZMod M) (by simp; omega)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; subst q
        exact ⟨Nat.prime_two, (show 2≤h by omega).trans (le_self_pow₀ (by omega) (by norm_num))⟩)
    (hp.half_fresh (by omega) h (le_refl _))
    (halfturn_ne_zero (StandingPrimes.circle_even (h:=h) (p:=p)))
    (halfturn_supported (StandingPrimes.circle_even (h:=h) (p:=p)))
  simp only [Finset.card_singleton] at hbound
  have hsep := excluded_separation (StandingPrimes.circle_even (h:=h) (p:=p)) (by omega : 0<h)
    hR hp.divides_circle hp.positive (fun _ => by simp; omega) h v ((M/2:ℕ) : ZMod M)
  have hnum := excluded_descent_numeric hn he
  have hL : (0:ℝ) ≤ excludedLength h p R M h := by positivity
  have hc : (0:ℝ) ≤ 1/((2:ℝ)^h*4) := by positivity
  calc
    _ = (excludedLength h p R M h:ℝ)*(1/(n:ℝ)^(3*h)) := by dsimp [h,M]; ring
    _ ≤ (excludedLength h p R M h:ℝ)*((1/((2:ℝ)^h*4))*pairDescentBound h (h/100) (n^3) n 1 h) :=
      mul_le_mul_of_nonneg_left hnum hL
    _ ≤ (1/((2:ℝ)^h*4))*(excludedLength h p R M h)*excludedCost h p M hp.divides_circle hp.positive h ((M/2:ℕ) : ZMod M) := by
      nlinarith [mul_le_mul_of_nonneg_left hbound (mul_nonneg hL hc)]
    _ ≤ _ := hsep

end FiniteCircle

end OAI
