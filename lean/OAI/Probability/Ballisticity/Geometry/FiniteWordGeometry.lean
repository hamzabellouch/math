import Mathlib
import OAI.Probability.Ballisticity.Geometry.SignedHeight
import OAI.Probability.Ballisticity.Crossings.HitWord

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma wordPath_append_prefix {d : ℕ} (x : Lattice d) (u v : List (Direction d))
    {n : ℕ} (hn : n ≤ u.length) : wordPath x (u ++ v) n = wordPath x u n := by
  induction u generalizing x n with
  | nil =>
    have : n = 0 := by simpa using hn
    simp [this]
  | cons e u ih =>
    cases n with
    | zero => simp
    | succ n =>
      simpa only [List.cons_append,wordPath] using ih (x+step e) (Nat.le_of_succ_le_succ hn)

lemma wordPath_append_suffix {d : ℕ} (x : Lattice d) (u v : List (Direction d))
    (n : ℕ) : wordPath x (u ++ v) (u.length+n) = wordPath (wordPath x u u.length) v n := by
  induction u generalizing x with
  | nil => simp [wordPath]
  | cons e u ih =>
    simpa only [List.cons_append,List.length_cons,Nat.succ_add,wordPath] using ih (x+step e)

lemma wordPath_after_end {d : ℕ} (x : Lattice d) (u : List (Direction d))
    {n : ℕ} (hn : u.length ≤ n) : wordPath x u n = wordPath x u u.length := by
  induction u generalizing x n with
  | nil => rfl
  | cons e u ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      simpa only [List.length_cons,wordPath] using ih (x+step e) (Nat.le_of_succ_le_succ hn)

lemma wordWeight_append {d : ℕ} (ω : Environment d) (x : Lattice d)
    (u v : List (Direction d)) :
    wordWeight ω x (u ++ v) = wordWeight ω x u * wordWeight ω (wordPath x u u.length) v := by
  induction u generalizing x with
  | nil => simp [wordWeight,wordPath]
  | cons e u ih => simp only [List.cons_append,wordWeight,List.length_cons,wordPath,ih,mul_assoc]

lemma wordPath_height_step {d : ℕ} (e : Direction d) (x : Lattice d)
    (w : List (Direction d)) (n : ℕ) :
    signedHeight e (wordPath x w (n+1)) ≤ signedHeight e (wordPath x w n)+1 := by
  rcases wordPath_step_or_stay x w n with h | ⟨g,h⟩
  · rw [h]; omega
  · rw [h]; exact signedHeight_step_le e _ g

lemma wordPath_hit_exact {d : ℕ} (e : Direction d) (x : Lattice d) (H : ℕ)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)) :
    signedHeight e (wordPath x w.val w.val.length) = signedHeight e x + H := by
  have htop : signedHeight e x + H ≤ signedHeight e (wordPath x w.val w.val.length) := by
    have h := w.property.1
    change dot (realPosition x) (realPosition (step e))+(H:ℝ) ≤
      dot (realPosition (wordPath x w.val w.val.length)) (realPosition (step e)) at h
    rw [signedHeight_projection,signedHeight_projection] at h
    exact_mod_cast h
  apply le_antisymm _ htop
  cases hlen : w.val.length with
  | zero => simpa only [hlen,wordPath_zero] using (show signedHeight e x ≤ signedHeight e x+H by omega)
  | succ n =>
    have h := (w.property.2 n (by omega)).2
    change dot (realPosition (wordPath x w.val n)) (realPosition (step e)) <
      dot (realPosition x) (realPosition (step e))+(H:ℝ) at h
    rw [signedHeight_projection,signedHeight_projection] at h
    have hn : signedHeight e (wordPath x w.val n) < signedHeight e x+H := by exact_mod_cast h
    have hs := wordPath_height_step e x w.val n
    omega

noncomputable def wordFirstHitTime {d : ℕ} (e : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d)) : ℕ :=
  if h : ∃ n, signedHeight e x+s ≤ signedHeight e (wordPath x w n) then Nat.find h else 0

noncomputable def wordFirstHitPosition {d : ℕ} (e : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d)) : Lattice d :=
  wordPath x w (wordFirstHitTime e x s w)

lemma wordFirstHitTime_spec {d : ℕ} (e : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d))
    (h : ∃ n, signedHeight e x+s ≤ signedHeight e (wordPath x w n)) :
    signedHeight e x+s ≤ signedHeight e (wordFirstHitPosition e x s w) := by
  simp only [wordFirstHitPosition,wordFirstHitTime,dite_eq_left h]
  exact Nat.find_spec h

lemma wordFirstHitTime_le {d : ℕ} (e : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d)) {n : ℕ}
    (h : signedHeight e x+s ≤ signedHeight e (wordPath x w n)) :
    wordFirstHitTime e x s w ≤ n := by
  simp only [wordFirstHitTime,dite_eq_left (show ∃ n, signedHeight e x+s ≤ signedHeight e (wordPath x w n) from ⟨n,h⟩)]
  exact Nat.find_min' _ h

lemma wordFirstHitTime_min {d : ℕ} (e : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d)) {n : ℕ} (hn : n < wordFirstHitTime e x s w) :
    signedHeight e (wordPath x w n) < signedHeight e x+s := by
  by_contra h
  exact (wordFirstHitTime_le e x s w (le_of_not_gt h)).not_gt hn

lemma wordFirstHitTime_zero {d : ℕ} (e : Direction d) (x : Lattice d)
    (w : List (Direction d)) : wordFirstHitTime e x 0 w = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply wordFirstHitTime_le
  simp

lemma wordFirstHitTime_endpoint {d : ℕ} (e : Direction d) (x : Lattice d) (H : ℕ)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)) :
    wordFirstHitTime e x H w.val = w.val.length := by
  have hh : signedHeight e x+(H:ℤ) ≤ signedHeight e (wordPath x w.val w.val.length) :=
    (wordPath_hit_exact e x H w).ge
  apply le_antisymm (wordFirstHitTime_le e x H w.val hh)
  by_contra h
  have hn : wordFirstHitTime e x H w.val < w.val.length := by omega
  have hp := (w.property.2 _ hn).2
  change dot (realPosition (wordFirstHitPosition e x H w.val)) (realPosition (step e)) <
    dot (realPosition x) (realPosition (step e))+(H:ℝ) at hp
  rw [signedHeight_projection,signedHeight_projection] at hp
  have hp' : signedHeight e (wordFirstHitPosition e x H w.val) < signedHeight e x+H := by exact_mod_cast hp
  exact hp'.not_ge (wordFirstHitTime_spec e x H w.val ⟨w.val.length,hh⟩)

lemma coordinate_mem_strip_iff {d : ℕ} (e : Direction d) (x y : Lattice d) (H : ℕ) :
    y ∈ Strip (realPosition (step e)) x H ↔
      signedHeight e x ≤ signedHeight e y ∧ signedHeight e y < signedHeight e x+H := by
  simp only [Strip,Set.mem_ofPred_eq,signedHeight_projection]
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2
  · rintro ⟨h1,h2⟩
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2

lemma coordinate_mem_upper_iff {d : ℕ} (e : Direction d) (x y : Lattice d) (H : ℕ) :
    y ∈ Upper (realPosition (step e)) x H ↔ signedHeight e x+H ≤ signedHeight e y := by
  simp only [Upper,Set.mem_ofPred_eq,signedHeight_projection]
  constructor <;> intro h <;> exact_mod_cast h

lemma wordPath_hit_append {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : HitWord (wordPath x u.val u.val.length)
      (Strip (realPosition (step e)) (wordPath x u.val u.val.length) m)
      (Upper (realPosition (step e)) (wordPath x u.val u.val.length) m)) :
    wordPath x (u.val++v.val) ∈ HitAt (Strip (realPosition (step e)) x ((h+m : ℕ) : ℝ))
      (Upper (realPosition (step e)) x ((h+m : ℕ) : ℝ)) (u.val++v.val).length := by
  have hy := wordPath_hit_exact e x h u
  constructor
  · rw [List.length_append,wordPath_append_suffix,coordinate_mem_upper_iff,
      wordPath_hit_exact e _ m v,hy,Nat.cast_add]
    omega
  · intro n hn
    rw [coordinate_mem_strip_iff]
    by_cases hu : n < u.val.length
    · rw [wordPath_append_prefix x u.val v.val hu.le]
      have hp := (coordinate_mem_strip_iff e x (wordPath x u.val n) h).mp (u.property.2 n hu)
      constructor
      · exact hp.1
      · push_cast; omega
    · have he : n = u.val.length+(n-u.val.length) := by omega
      rw [he,wordPath_append_suffix]
      have hv : n-u.val.length < v.val.length := by simp only [List.length_append] at hn; omega
      have hp := (coordinate_mem_strip_iff e _ _ m).mp (v.property.2 _ hv)
      rw [hy] at hp
      constructor <;> push_cast <;> omega

lemma wordFirstHitTime_eq {d : ℕ} (e : Direction d) (x : Lattice d) (s : ℕ)
    (w : List (Direction d)) (n : ℕ)
    (hn : signedHeight e x+s ≤ signedHeight e (wordPath x w n))
    (hmin : ∀ i < n, signedHeight e (wordPath x w i) < signedHeight e x+s) :
    wordFirstHitTime e x s w = n := by
  apply le_antisymm (wordFirstHitTime_le e x s w hn)
  by_contra hc
  have hi : wordFirstHitTime e x s w < n := by omega
  exact (hmin _ hi).not_ge (wordFirstHitTime_spec e x s w ⟨n,hn⟩)

lemma wordFirstHitTime_append_prefix {d : ℕ} (e : Direction d) (x : Lattice d)
    (h s : ℕ) (hs : s ≤ h)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : List (Direction d)) :
    wordFirstHitTime e x s (u.val++v) = wordFirstHitTime e x s u.val := by
  have hend : signedHeight e x+s ≤ signedHeight e (wordPath x u.val u.val.length) := by
    rw [wordPath_hit_exact e x h u]; omega
  have hn := wordFirstHitTime_le e x s u.val hend
  apply wordFirstHitTime_eq
  · rw [wordPath_append_prefix x u.val v hn]
    exact wordFirstHitTime_spec e x s u.val ⟨u.val.length,hend⟩
  · intro i hi
    rw [wordPath_append_prefix x u.val v (hi.le.trans hn)]
    exact wordFirstHitTime_min e x s u.val hi

lemma wordFirstHitPosition_append_prefix {d : ℕ} (e : Direction d) (x : Lattice d)
    (h s : ℕ) (hs : s ≤ h)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : List (Direction d)) :
    wordFirstHitPosition e x s (u.val++v) = wordFirstHitPosition e x s u.val := by
  rw [wordFirstHitPosition,wordFirstHitTime_append_prefix e x h s hs u v]
  apply wordPath_append_prefix
  apply wordFirstHitTime_le
  rw [wordPath_hit_exact e x h u]
  omega

lemma wordFirstHitTime_append_suffix {d : ℕ} (e : Direction d) (x : Lattice d)
    (h m t : ℕ) (ht : t ≤ m)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : HitWord (wordPath x u.val u.val.length)
      (Strip (realPosition (step e)) (wordPath x u.val u.val.length) m)
      (Upper (realPosition (step e)) (wordPath x u.val u.val.length) m)) :
    wordFirstHitTime e x (h+t) (u.val++v.val) =
      u.val.length+wordFirstHitTime e (wordPath x u.val u.val.length) t v.val := by
  have hy := wordPath_hit_exact e x h u
  have hend : signedHeight e (wordPath x u.val u.val.length)+t ≤
      signedHeight e (wordPath (wordPath x u.val u.val.length) v.val v.val.length) := by
    rw [wordPath_hit_exact e _ m v]; omega
  apply wordFirstHitTime_eq
  · rw [wordPath_append_suffix,Nat.cast_add,← add_assoc,← hy]
    exact wordFirstHitTime_spec e _ t v.val ⟨v.val.length,hend⟩
  · intro i hi
    by_cases hui : i < u.val.length
    · rw [wordPath_append_prefix x u.val v.val hui.le]
      have hp := ((coordinate_mem_strip_iff e x _ h).mp (u.property.2 _ hui)).2
      push_cast; omega
    · have he : i = u.val.length+(i-u.val.length) := by omega
      rw [he,wordPath_append_suffix,Nat.cast_add,← add_assoc,← hy]
      apply wordFirstHitTime_min
      omega

lemma wordFirstHitPosition_append_suffix {d : ℕ} (e : Direction d) (x : Lattice d)
    (h m t : ℕ) (ht : t ≤ m)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : HitWord (wordPath x u.val u.val.length)
      (Strip (realPosition (step e)) (wordPath x u.val u.val.length) m)
      (Upper (realPosition (step e)) (wordPath x u.val u.val.length) m)) :
    wordFirstHitPosition e x (h+t) (u.val++v.val) =
      wordFirstHitPosition e (wordPath x u.val u.val.length) t v.val := by
  rw [wordFirstHitPosition,wordFirstHitTime_append_suffix e x h m t ht u v,
    wordPath_append_suffix]
  rfl

end DirectionalTransience

end

end OAI
