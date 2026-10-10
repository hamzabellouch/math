import Mathlib

namespace OAI

namespace CurrentKS.RationalGridSize

def Grid (D : ℕ) (q : ℚ) : Prop := q.den ∣ D

lemma Grid.zero (D : ℕ) : Grid D 0 := by simp [Grid]
lemma Grid.one (D : ℕ) : Grid D 1 := by simp [Grid]
lemma Grid.integer (D : ℕ) (k : ℤ) : Grid D (k:ℚ) := by simp [Grid]
lemma Grid.neg {D : ℕ} {q : ℚ} (hq : Grid D q) : Grid D (-q) := by
  simpa only [Grid,Rat.neg_den] using hq
lemma Grid.add {D : ℕ} {q r : ℚ} (hq : Grid D q) (hr : Grid D r) : Grid D (q+r) :=
  (Rat.add_den_dvd_lcm q r).trans (Nat.lcm_dvd hq hr)
lemma Grid.sub {D : ℕ} {q r : ℚ} (hq : Grid D q) (hr : Grid D r) : Grid D (q-r) :=
  (Rat.sub_den_dvd_lcm q r).trans (Nat.lcm_dvd hq hr)
lemma Grid.mul_integer {D : ℕ} {q : ℚ} (hq : Grid D q) (k : ℤ) : Grid D (q*(k:ℚ)) := by
  apply (Rat.mul_den_dvd q (k:ℚ)).trans
  simpa only [Grid,Rat.den_intCast,mul_one] using hq

lemma Grid.den_le {D : ℕ} (hD : 0 < D) {q : ℚ} (hq : Grid D q) : q.den ≤ D :=
  Nat.le_of_dvd hD hq

lemma numerator_le_den {q : ℚ} (hq : |q| ≤ 1) : q.num.natAbs ≤ q.den := by
  have hd : (0:ℚ) < q.den := by exact_mod_cast q.den_pos
  have hn : |(q.num:ℚ)|/(q.den:ℚ) ≤ 1 := by
    calc
      |(q.num:ℚ)|/(q.den:ℚ) = |(q.num:ℚ)/(q.den:ℚ)| := by rw [abs_div,abs_of_pos hd]
      _ = |q| := congrArg abs (Rat.num_div_den q)
      _ ≤ 1 := hq
  have hn' : |(q.num:ℚ)| ≤ (q.den:ℚ) := (div_le_one hd).mp hn
  have he : ((q.num.natAbs:ℕ):ℚ)=|(q.num:ℚ)| := by simp
  rw [← he] at hn'
  exact_mod_cast hn'

lemma coordinate_size_bound {D : ℕ} (hD : 0 < D) {q : ℚ}
    (hgrid : Grid D q) (hq : |q| ≤ 1) :
    q.num.natAbs ≤ D ∧ q.den ≤ D :=
  ⟨(numerator_le_den hq).trans (hgrid.den_le hD),hgrid.den_le hD⟩

open scoped BigOperators

def bitSize (q : ℚ) : ℕ := q.num.natAbs.size+q.den.size

lemma coordinate_bit_bound {D : ℕ} (hD : 0 < D) {q : ℚ}
    (hgrid : Grid D q) (hq : |q| ≤ 1) : bitSize q ≤ 2*D.size := by
  obtain ⟨hn,hd⟩ := coordinate_size_bound hD hgrid hq
  have hn' := Nat.size_le_size hn
  have hd' := Nat.size_le_size hd
  unfold bitSize
  omega

lemma size_mul_le (m n : ℕ) : (m*n).size ≤ m.size+n.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self m) (Nat.lt_size_self n)

lemma size_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∏ i∈s,f i).size ≤ 1+∑ i∈s,(f i).size := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    have hm := size_mul_le (f a) (∏ i∈s,f i)
    omega

end CurrentKS.RationalGridSize

end OAI
