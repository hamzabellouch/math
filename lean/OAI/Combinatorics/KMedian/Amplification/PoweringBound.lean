import Mathlib
import OAI.Combinatorics.KMedian.Amplification.Majority
import OAI.Combinatorics.KMedian.Amplification.PoweringConstruction

namespace OAI

section Inline_PCPPoweringBound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

lemma geometric_tail_bound (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (h : p+q=1) (n : ℕ) :
    (1+(n:ℝ)*p)*q^n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hqp := pow_nonneg hq n
    have hs : (1+((n:ℝ)+1)*p)*q ≤ 1+(n:ℝ)*p := by
      rw [show q=1-p by linarith]
      nlinarith [mul_nonneg (add_nonneg hn zero_le_one) (mul_nonneg hp hp)]
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    calc
      _ = ((1+((n:ℝ)+1)*p)*q)*q^n := by ring
      _ ≤ (1+(n:ℝ)*p)*q^n := mul_le_mul_of_nonneg_right hs hqp
      _ ≤ 1 := ih

namespace PortGraph
lemma totalMass_half (t : ℕ) : 1/2 ≤ totalMass t t := by
  have h := geometric_tail_bound (Stopped.stopping t) (Stopped.survival t)
    (Stopped.stopping_nonneg t) (Stopped.survival_nonneg t)
    (by linarith [Stopped.survival_add_stopping t]) (t+1)
  have he : ((t+1:ℕ):ℝ)*Stopped.stopping t = 1 := by
    unfold Stopped.stopping
    push_cast
    have ht : (t:ℝ)+1 ≠ 0 := by positivity
    field_simp
  rw [he] at h
  rw [totalMass_eq]
  linarith
end PortGraph

lemma powering_arithmetic (u m q r : ℝ) (hu : 0 ≤ u) (hm : 1/2 ≤ m)
    (hq : 0 < q) (hr : 0 ≤ r)
    (h : (u*(m/q)^2)^2 ≤ r*(20*u+16*u^2)) :
    min u 1 ≤ 576*q^4*r := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hm2 : 1/4 ≤ m^2 := by nlinarith
  have hm4 : 1/16 ≤ m^4 := by nlinarith [sq_nonneg (m^2-1/4)]
  have he : 16*q^4*(u*(m/q)^2)^2 = 16*u^2*m^4 := by
    field_simp
  have hlow : u^2 ≤ 16*q^4*(u*(m/q)^2)^2 := by
    rw [he]
    nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 16*m^4-1 by linarith)]
  have hh := hlow.trans (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 16*q^4))
  by_cases hzero : u=0
  · subst u; simp; positivity
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hzero)
  have hc : 0 ≤ 16*q^4*r := by positivity
  by_cases hu1 : u ≤ 1
  · rw [min_eq_left hu1]
    have hub : 20*u+16*u^2 ≤ 36*u := by nlinarith
    have hh' : u^2 ≤ (576*q^4*r)*u := by
      calc
        _ ≤ 16*q^4*(r*(20*u+16*u^2)) := hh
        _ = (16*q^4*r)*(20*u+16*u^2) := by ring
        _ ≤ (16*q^4*r)*(36*u) := mul_le_mul_of_nonneg_left hub hc
        _ = _ := by ring
    nlinarith
  · rw [min_eq_right (le_of_not_ge hu1)]
    have hub : 20*u+16*u^2 ≤ 36*u^2 := by nlinarith
    have hh' : u^2 ≤ (576*q^4*r)*u^2 := by
      calc
        _ ≤ 16*q^4*(r*(20*u+16*u^2)) := hh
        _ = (16*q^4*r)*(20*u+16*u^2) := by ring
        _ ≤ (16*q^4*r)*(36*u^2) := mul_le_mul_of_nonneg_left hub hc
        _ = _ := by ring
    exact (le_mul_iff_one_le_right (sq_pos_of_pos hup)).mp (by simpa only [mul_comm] using hh')

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A)

theorem powered_amplification (hG : G.Contracts (1/2)) (t : ℕ) (ht : 1 ≤ t)
    (a : V → Advice D A (2*t+2)) :
    min ((t:ℝ)*testRate (C.Bad (G.plurality a t t))) 1 ≤
      576*(Fintype.card A:ℝ)^4 * (C.powered (cap := 2*t+2) t).rejection a := by
  have hh := C.powered_sound hG a t t (by omega)
  have hd := testRate_nonneg (C.Bad (G.plurality a t t))
  have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hc : ((2*t+2:ℕ):ℝ) ≤ 4*(t:ℝ) := by push_cast; linarith
  have hc0 : (0:ℝ) ≤ (2*t+2:ℕ) := Nat.cast_nonneg _
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have hc2 : (((2*t+2:ℕ):ℝ))^2 ≤ 16*(t:ℝ)^2 := by nlinarith
  have hbound : 5*((2*t+2:ℕ):ℝ)*testRate (C.Bad (G.plurality a t t)) +
      (((2*t+2:ℕ):ℝ))^2*(testRate (C.Bad (G.plurality a t t)))^2 ≤
      20*((t:ℝ)*testRate (C.Bad (G.plurality a t t))) +
      16*((t:ℝ)*testRate (C.Bad (G.plurality a t t)))^2 := by
    have h1 := mul_le_mul_of_nonneg_right hc hd
    have h2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (testRate (C.Bad (G.plurality a t t))))
    nlinarith
  exact powering_arithmetic _ _ _ _ (mul_nonneg ht0 hd) (PortGraph.totalMass_half t)
    (Nat.cast_pos.mpr Fintype.card_pos) (testRate_nonneg _) (hh.trans
      (mul_le_mul_of_nonneg_left hbound (testRate_nonneg _)))

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringBound

end OAI
