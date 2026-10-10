import OAI.NumberTheory.TwoPoint.Fourier.MajorArcResidues

namespace OAI

/-! Gcd strata of a rational additive phase. The unit character expansion
on the quotient is supported on exactly one divisor of the modulus. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma major_arc_reduced_unit_iff (q d n : ℕ) (hq : 0 < q)
    (hdq : d∣q) (hdn : d∣n) :
    IsUnit ((n/d:ℕ) : ZMod (q/d)) ↔ n.gcd q=d := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  have hquot : 0 < q/d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd
  let : NeZero (q/d) := ⟨hquot.ne'⟩
  rw [ZMod.isUnit_iff_coprime]
  constructor
  · intro hc
    have he : n.gcd q=d*((n/d).gcd (q/d)) := by
      conv_lhs => rw [←Nat.mul_div_cancel' hdn,←Nat.mul_div_cancel' hdq]
      exact Nat.gcd_mul_left d (n/d) (q/d)
    simpa only [hc.gcd_eq_one,mul_one] using he
  · intro he
    have hc := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right n hq)
    rwa [he] at hc

lemma major_arc_gcd_phase (q n : ℕ) (hq : 0 < q) (r : ℤ) :
    additiveCharacter ((r:ℝ)/((q/n.gcd q:ℕ):ℝ)) (n/n.gcd q) =
      additiveCharacter ((r:ℝ)/q) n := by
  have hd : 0 < n.gcd q := Nat.gcd_pos_of_pos_right n hq
  have hd0 : (n.gcd q:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hq0 : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  have hncast : ((n/n.gcd q:ℕ):ℝ)=(n:ℝ)/(n.gcd q:ℝ) :=
    Nat.cast_div (Nat.gcd_dvd_left n q) hd0
  have hqcast : ((q/n.gcd q:ℕ):ℝ)=(q:ℝ)/(n.gcd q:ℝ) :=
    Nat.cast_div (Nat.gcd_dvd_right n q) hd0
  unfold additiveCharacter
  rw [hncast,hqcast]
  congr 2
  field_simp

/-- The reduced unit projector partitions every positive argument, including
arguments in nonunit residue classes and reduced modulus one. -/
lemma major_arc_gcd_partition (q n : ℕ) (hq : 0 < q) (_hn : 0 < n)
    (r : ℤ) :
    (∑ d ∈ q.divisors, if d∣n then
      if IsUnit ((n/d:ℕ):ZMod (q/d)) then
        additiveCharacter ((r:ℝ)/((q/d:ℕ):ℝ)) (n/d) else 0 else 0) =
      additiveCharacter ((r:ℝ)/q) n := by
  rw [sum_eq_single (n.gcd q)]
  · rw [ite_eq_left (Nat.gcd_dvd_left n q),
      ite_eq_left ((major_arc_reduced_unit_iff q (n.gcd q) n hq
        (Nat.gcd_dvd_right n q) (Nat.gcd_dvd_left n q)).mpr rfl)]
    exact major_arc_gcd_phase q n hq r
  · intro d hd hne
    by_cases hdn : d∣n
    · rw [ite_eq_left hdn,ite_eq_right]
      intro hu
      exact hne ((major_arc_reduced_unit_iff q d n hq (Nat.mem_divisors.mp hd).1 hdn).mp hu).symm
    · rw [ite_eq_right hdn]
  · intro hnot
    exact (hnot (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n q,hq.ne'⟩)).elim

end TwoPointCorrelations

end OAI
