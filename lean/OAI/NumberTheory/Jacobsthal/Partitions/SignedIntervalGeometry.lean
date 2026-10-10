import OAI.NumberTheory.Jacobsthal.Primes.PrimeIntervalFlags

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

noncomputable def retainedLength (a b t : ℝ) : ℝ := if t ≤ b-a then b-a else 0

lemma retainedLength_nonneg {a b t : ℝ} (ht : 0 ≤ t) : 0 ≤ retainedLength a b t := by
  unfold retainedLength
  split_ifs with h
  · linarith
  · exact le_refl 0

lemma retainedLength_lower (a b t : ℝ) (ht : 0 ≤ t) :
    max (b-a) 0-t ≤ retainedLength a b t := by
  unfold retainedLength
  split_ifs with h
  · rw [max_eq_left (by linarith : 0 ≤ b-a)]
    linarith
  · have hm : max (b-a) 0 ≤ t := by apply max_le <;> linarith
    linarith

lemma signed_trim_length {x y t : ℝ} (hxy : x ≤ y) (ht : 0 ≤ t) :
    y-x ≤ max (y-max x t) 0+max (-x-max (-y) t) 0+2*t := by
  simp only [max_def]
  split_ifs <;> linarith

lemma signed_retained_length {x y t : ℝ} (hxy : x ≤ y) (ht : 0 ≤ t) :
    y-x-4*t ≤ retainedLength (max x t) y t + retainedLength (max (-y) t) (-x) t := by
  have hp := retainedLength_lower (max x t) y t ht
  have hn := retainedLength_lower (max (-y) t) (-x) t ht
  have htrim := signed_trim_length hxy ht
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
