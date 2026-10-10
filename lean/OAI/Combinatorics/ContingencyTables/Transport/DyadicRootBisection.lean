import OAI.Combinatorics.ContingencyTables.Transport.RationalRootBisection
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeFraction

namespace OAI

/-! # Integer implementation of the correction-root bisection

The two interval endpoints share one dyadic denominator. Every comparison
is an inequality between natural powers and products. This is the literal
integer algorithm to which the rational correction analysis is applied.
-/

namespace ContingencyTables.DyadicRootBisection

open MatchingFPRAS

abbrev State := (ℕ×ℕ)×ℕ

def value (z : State) : ℚ×ℚ := ((z.1.1:ℚ)/z.2,(z.1.2:ℚ)/z.2)

def advance (c : TreeFraction.Fraction) (s : ℕ) (z : State) : State :=
  if (z.1.1+z.1.2)^s*c.2 ≤ c.1*(2*z.2)^s
  then ((z.1.1+z.1.2,2*z.1.2),2*z.2)
  else ((2*z.1.1,z.1.1+z.1.2),2*z.2)

def run (c : TreeFraction.Fraction) (s : ℕ) : ℕ→State
  | 0=>((0,8),1)
  | n+1=>advance c s (run c s n)

def output (c : TreeFraction.Fraction) (s n : ℕ) : TreeFraction.Fraction :=
  let z:=run c s n
  TreeFraction.normalize (z.1.1+z.1.2,2*z.2)

lemma compare_iff (a d p q s : ℕ) (hd : 0<d) (hq : 0<q) :
    ((a:ℚ)/d)^s ≤ (p:ℚ)/q ↔ a^s*q≤p*d^s := by
  rw [div_pow,div_le_div_iff₀ (pow_pos (by exact_mod_cast hd) _)
    (by exact_mod_cast hq)]
  norm_cast

lemma advance_denominator (c : TreeFraction.Fraction) (s : ℕ) (z : State) :
    (advance c s z).2=2*z.2 := by
  unfold advance
  split_ifs <;> rfl

lemma run_denominator (c : TreeFraction.Fraction) (s n : ℕ) :
    (run c s n).2=2^n := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [run,advance_denominator,ih,pow_succ,mul_comm]

lemma advance_bounds (c : TreeFraction.Fraction) (s : ℕ) (z : State)
    (ha : z.1.1≤8*z.2) (hb : z.1.2≤8*z.2) :
    (advance c s z).1.1≤8*(advance c s z).2 ∧
      (advance c s z).1.2≤8*(advance c s z).2 := by
  unfold advance
  split_ifs <;> dsimp only <;> omega

lemma run_bounds (c : TreeFraction.Fraction) (s n : ℕ) :
    (run c s n).1.1≤8*2^n ∧ (run c s n).1.2≤8*2^n := by
  induction n with
  | zero=>norm_num [run]
  | succ n ih=>
    have h:=advance_bounds c s (run c s n)
      (by simpa only [run_denominator] using ih.1)
      (by simpa only [run_denominator] using ih.2)
    change (run c s (n+1)).1.1≤8*(run c s (n+1)).2 ∧
      (run c s (n+1)).1.2≤8*(run c s (n+1)).2 at h
    simpa only [run_denominator] using h

lemma value_advance (c : TreeFraction.Fraction) (hc : 0<c.2)
    (s : ℕ) (z : State) (hz : 0<z.2) :
    value (advance c s z)=
      let ab:=value z
      let mid:=(ab.1+ab.2)/2
      if mid^s≤TreeFraction.val c then (mid,ab.2) else (ab.1,mid) := by
  have hD : (z.2:ℚ)≠0 := by exact_mod_cast hz.ne'
  have hm : (((z.1.1:ℚ)/z.2)+((z.1.2:ℚ)/z.2))/2=
      ((z.1.1+z.1.2:ℕ):ℚ)/((2*z.2:ℕ):ℚ) := by
    push_cast
    field_simp [hD]
  have hleft : ((2*z.1.1:ℕ):ℚ)/((2*z.2:ℕ):ℚ)=(z.1.1:ℚ)/z.2 := by
    push_cast
    field_simp [hD]
  have hright : ((2*z.1.2:ℕ):ℚ)/((2*z.2:ℕ):ℚ)=(z.1.2:ℚ)/z.2 := by
    push_cast
    field_simp [hD]
  have ht:=compare_iff (z.1.1+z.1.2) (2*z.2) c.1 c.2 s (by omega) hc
  dsimp only [value,TreeFraction.val]
  rw [hm]
  by_cases h : (z.1.1+z.1.2)^s*c.2≤c.1*(2*z.2)^s
  · simp only [advance,h,ite_true,ht.mpr h,hright]
  · have hr := mt ht.mp h
    simp only [advance,h,ite_false,hr,hleft]

/-- Every integer execution is the rational bisection used by the
already proved relative-error estimate. -/
theorem run_value (c : TreeFraction.Fraction) (hc : 0<c.2) (s n : ℕ) :
    value (run c s n)=RationalRootBisection.interval (TreeFraction.val c) s n := by
  induction n with
  | zero=>norm_num [run,value,RationalRootBisection.interval]
  | succ n ih=>
    rw [run,value_advance c hc s _ (by rw [run_denominator]; positivity),ih]
    rfl

theorem output_value (c : TreeFraction.Fraction) (hc : 0<c.2) (s n : ℕ) :
    TreeFraction.val (output c s n)=
      RationalRootBisection.midpoint (TreeFraction.val c) s n := by
  have he:=run_value c hc s n
  unfold output
  rw [TreeFraction.normalize_val]
  unfold RationalRootBisection.midpoint
  rw [←he]
  dsimp only [value,TreeFraction.val]
  have hD : ((run c s n).2:ℚ)≠0 := by rw [run_denominator]; positivity
  push_cast
  field_simp [hD]

theorem output_denominator_pos (c : TreeFraction.Fraction) (s n : ℕ) :
    0<(output c s n).2 := TreeFraction.normalize_den_pos _

end ContingencyTables.DyadicRootBisection

end OAI
