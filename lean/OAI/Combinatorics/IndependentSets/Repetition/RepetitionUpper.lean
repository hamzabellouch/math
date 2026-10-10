import Mathlib

namespace OAI

namespace IndependentSetsGames.Soundness.RepetitionUpper

def bernoulliAverage (p : Rat) : Nat → (Nat → Rat) → Rat
  | 0, f => f 0
  | n + 1, f =>
      (1 - p) * bernoulliAverage p n f +
        p * bernoulliAverage p n (fun k => f (k + 1))

theorem bernoulliAverage_scale (p c : Rat) (n : Nat) (f : Nat → Rat) :
    bernoulliAverage p n (fun k => c * f k) = c * bernoulliAverage p n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [bernoulliAverage, ih]
      grind

theorem bernoulliAverage_geometric (p a : Rat) (n : Nat) :
    bernoulliAverage p n (fun k => a ^ k) = (1 - p * (1 - a)) ^ n := by
  induction n with
  | zero => simp [bernoulliAverage]
  | succ n ih =>
      simp only [bernoulliAverage]
      have hs : (fun k : Nat => a ^ (k + 1)) = fun k => a * a ^ k := by
        funext k
        rw [Rat.pow_succ, Rat.mul_comm]
      rw [hs, bernoulliAverage_scale, ih, Rat.pow_succ]
      grind

theorem bernoulliAverage_mono (p : Rat) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : Nat) (f g : Nat → Rat) (h : ∀ k, f k ≤ g k) :
    bernoulliAverage p n f ≤ bernoulliAverage p n g := by
  induction n generalizing f g with
  | zero => exact h 0
  | succ n ih =>
      have hleft := ih f g h
      have hright := ih (fun k => f (k + 1)) (fun k => g (k + 1))
        (fun k => h (k + 1))
      have hnp : 0 ≤ 1 - p := by grind
      have hl := Rat.mul_le_mul_of_nonneg_left hleft hnp
      have hr := Rat.mul_le_mul_of_nonneg_left hright hp
      simp only [bernoulliAverage]
      grind

theorem success_le_geometric
    (p a success : Rat) (n : Nat) (conditionalSuccess : Nat → Rat)
    (hp : 0 ≤ p) (hp' : p ≤ 1)
    (conditional : ∀ k, conditionalSuccess k ≤ a ^ k)
    (averaged : success ≤ bernoulliAverage p n conditionalSuccess) :
    success ≤ (1 - p * (1 - a)) ^ n := by
  have h := bernoulliAverage_mono p hp hp' n conditionalSuccess
    (fun k => a ^ k) conditional
  rw [bernoulliAverage_geometric] at h
  exact Rat.le_trans averaged h

theorem pow_mono_nonneg (x y : Rat) (hx : 0 ≤ x) (hxy : x ≤ y) (n : Nat) :
    x ^ n ≤ y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hy : 0 ≤ y := Rat.le_trans hx hxy
      have hp : 0 ≤ x ^ n := Rat.pow_nonneg hx
      have h₁ := Rat.mul_le_mul_of_nonneg_left hxy hp
      have h₂ := Rat.mul_le_mul_of_nonneg_right ih hy
      simp only [Rat.pow_succ]
      exact Rat.le_trans h₁ h₂

def zeroProbability (d : Nat) : Rat := (1 / 2 : Rat) ^ d

theorem zeroProbability_nonneg (d : Nat) : 0 ≤ zeroProbability d := by
  exact Rat.pow_nonneg (by grind)

theorem zeroProbability_le_one (d : Nat) : zeroProbability d ≤ 1 := by
  induction d with
  | zero => simp [zeroProbability]
  | succ d ih =>
      have hp := zeroProbability_nonneg d
      simp only [zeroProbability, Rat.pow_succ] at *
      grind

theorem zeroProbability_antitone (d L : Nat) (hd : d ≤ L) :
    zeroProbability L ≤ zeroProbability d := by
  induction L with
  | zero =>
      have : d = 0 := by omega
      subst d
      exact Rat.le_refl
  | succ L ih =>
      by_cases heq : d = L + 1
      · subst d
        exact Rat.le_refl
      · have hdL : d ≤ L := by omega
        have h := ih hdL
        have hp := zeroProbability_nonneg L
        have hs : zeroProbability (L + 1) ≤ zeroProbability L := by
          simp only [zeroProbability, Rat.pow_succ] at *
          grind
        exact Rat.le_trans hs h

theorem geometric_le_dimension_bound (d L n : Nat) (hd : d ≤ L)
    (a : Rat) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (1 - zeroProbability d * (1 - a)) ^ n ≤
      (1 - zeroProbability L * (1 - a)) ^ n := by
  have hp := zeroProbability_nonneg d
  have hp' := zeroProbability_le_one d
  have hdL := zeroProbability_antitone d L hd
  have hna : 0 ≤ 1 - a := by grind
  have hprod := Rat.mul_le_mul_of_nonneg_right hdL hna
  have hnprod := Rat.mul_le_mul_of_nonneg_right hp' hna
  apply pow_mono_nonneg
  · grind
  · grind

theorem projection_upper_bound
    (d L n : Nat) (hd : d ≤ L) (a success : Rat)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (conditionalSuccess : Nat → Rat)
    (conditional : ∀ k, conditionalSuccess k ≤ a ^ k)
    (averaged : success ≤ bernoulliAverage (zeroProbability d) n conditionalSuccess) :
    success ≤ (1 - zeroProbability L * (1 - a)) ^ n := by
  have hs := success_le_geometric (zeroProbability d) a success n
    conditionalSuccess (zeroProbability_nonneg d) (zeroProbability_le_one d)
    conditional averaged
  exact Rat.le_trans hs (geometric_le_dimension_bound d L n hd a ha ha')

def decoderThreshold (theta : Rat) (q : Nat) : Rat := theta ^ 3 / (64 * (q : Rat))

theorem decoderThreshold_pos (theta : Rat) (q : Nat)
    (htheta : 0 < theta) (hq : 0 < q) : 0 < decoderThreshold theta q := by
  have hq' : (0 : Rat) < (q : Rat) := Rat.natCast_pos.mpr hq
  have ht := Rat.pow_pos (n := 3) htheta
  have hd : (0 : Rat) < 64 * (q : Rat) := by grind
  unfold decoderThreshold
  apply (Rat.lt_div_iff hd).mpr
  simpa using ht

theorem exists_pos_nat_gt (x : Rat) : ∃ n : Nat, 0 < n ∧ x < (n : Rat) := by
  refine ⟨x.ceil.toNat + 1, by omega, ?_⟩
  have hceil := Rat.le_ceil (x := x)
  have hint : x.ceil ≤ (x.ceil.toNat : Int) := by omega
  have hcast := Rat.intCast_le_intCast.mpr hint
  simp only [Rat.intCast_natCast] at hcast
  rw [Rat.natCast_add, Rat.natCast_ofNat]
  grind

theorem power_mul_growth_le_one (b : Rat) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (n : Nat) : b ^ n * (1 + (n : Rat) * (1 - b)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn := Rat.natCast_nonneg (a := n)
      have hc : 0 ≤ 1 - b := by grind
      have hnc : 0 ≤ ((n : Rat) + 1) * (1 - b) :=
        Rat.mul_nonneg (by grind) hc
      have hscaled := Rat.mul_le_mul_of_nonneg_right hb' hnc
      have hstep : b * (1 + ((n : Rat) + 1) * (1 - b)) ≤
          1 + (n : Rat) * (1 - b) := by grind
      have hprod := Rat.mul_le_mul_of_nonneg_left hstep (Rat.pow_nonneg (n := n) hb)
      simp only [Rat.pow_succ, Rat.natCast_add, Rat.natCast_ofNat]
      grind

theorem exists_power_lt (b threshold : Rat) (hb : 0 ≤ b) (hb' : b < 1)
    (ht : 0 < threshold) : ∃ n : Nat, 0 < n ∧ b ^ n < threshold := by
  have hc : 0 < 1 - b := by grind
  have hden : 0 < threshold * (1 - b) := Rat.mul_pos ht hc
  obtain ⟨n, hn, hlarge⟩ := exists_pos_nat_gt (1 / (threshold * (1 - b)))
  refine ⟨n, hn, ?_⟩
  have hlarge' := (Rat.div_lt_iff hden).mp hlarge
  have hn' := Rat.natCast_nonneg (a := n)
  have hg : 0 ≤ 1 + (n : Rat) * (1 - b) := by
    have h := Rat.mul_nonneg hn' (Rat.le_of_lt hc)
    grind
  have hbnd := power_mul_growth_le_one b hb (Rat.le_of_lt hb') n
  apply Rat.not_le.mp
  intro hbad
  have hmul := Rat.mul_le_mul_of_nonneg_right hbad hg
  grind

theorem zeroProbability_pos (d : Nat) : 0 < zeroProbability d := by
  exact Rat.pow_pos (by grind)

theorem exists_repetition_length (L q : Nat) (a theta : Rat)
    (ha : 0 ≤ a) (ha' : a < 1) (htheta : 0 < theta) (hq : 0 < q) :
    ∃ t : Nat, 0 < t ∧
      (1 - zeroProbability L * (1 - a)) ^ t < decoderThreshold theta q := by
  have hp := zeroProbability_pos L
  have hp' := zeroProbability_le_one L
  have hc : 0 < 1 - a := by grind
  have hmul := Rat.mul_le_mul_of_nonneg_right hp' (Rat.le_of_lt hc)
  have hpos := Rat.mul_pos hp hc
  apply exists_power_lt
  · grind
  · grind
  · exact decoderThreshold_pos theta q htheta hq

theorem soundness_of_bounds
    {Labeling Strategy : Type} (acceptance : Labeling → Rat)
    (success : Strategy → Rat) (delta lower upperBound : Rat)
    (extraction : ∀ labeling, delta < acceptance labeling →
      ∃ strategy, lower ≤ success strategy)
    (upper : ∀ strategy, success strategy ≤ upperBound)
    (gap : upperBound < lower) :
    ∀ labeling, acceptance labeling ≤ delta := by
  intro labeling
  apply Rat.not_lt.mp
  intro hbad
  obtain ⟨strategy, hlow⟩ := extraction labeling hbad
  have h : lower ≤ upperBound := Rat.le_trans hlow (upper strategy)
  exact (Rat.not_lt.mpr h) gap

theorem soundness_from_repetition
    {Labeling Strategy : Type} (acceptance : Labeling → Rat)
    (success : Strategy → Rat) (dimension : Strategy → Nat)
    (conditionalSuccess : Strategy → Nat → Rat)
    (delta a theta : Rat) (q L t : Nat) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (dimension_le : ∀ strategy, dimension strategy ≤ L)
    (conditional : ∀ strategy k, conditionalSuccess strategy k ≤ a ^ k)
    (averaged : ∀ strategy, success strategy ≤
      bernoulliAverage (zeroProbability (dimension strategy)) t
        (conditionalSuccess strategy))
    (extraction : ∀ labeling, delta < acceptance labeling →
      ∃ strategy, decoderThreshold theta q ≤ success strategy)
    (gap : (1 - zeroProbability L * (1 - a)) ^ t < decoderThreshold theta q) :
    ∀ labeling, acceptance labeling ≤ delta := by
  apply soundness_of_bounds acceptance success delta (decoderThreshold theta q)
    ((1 - zeroProbability L * (1 - a)) ^ t) extraction
  · intro strategy
    exact projection_upper_bound (dimension strategy) L t (dimension_le strategy)
      a (success strategy) ha ha' (conditionalSuccess strategy)
      (conditional strategy) (averaged strategy)
  · exact gap

end IndependentSetsGames.Soundness.RepetitionUpper

end OAI
