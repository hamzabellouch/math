import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedDeficitPositivity

open Filter Set
open scoped Topology

theorem mass_lower_bound {b : ℝ → ℝ} {l u m : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hc : ContinuousOn b (Icc l u)) (hbl : m ≤ b l)
    (hd : ∀ t ∈ Ioo l u, ∃ v, HasDerivAt (fun s => s * b s) v t ∧ m ≤ v) :
    m ≤ b u := by
  have hcM : ContinuousOn (fun s => s * b s) (Icc l u) := continuousOn_id.mul hc
  have hdM : DifferentiableOn ℝ (fun s => s * b s) (interior (Icc l u)) := by
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨v, hv, _⟩ := hd t ht
    exact hv.differentiableAt.differentiableWithinAt
  have hder : ∀ t ∈ interior (Icc l u), m ≤ deriv (fun s => s * b s) t := by
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨v, hv, hm⟩ := hd t ht
    simpa only [hv.deriv] using hm
  have h := (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv hcM hdM hder
    l ⟨le_rfl, hlu⟩ u ⟨hlu, le_rfl⟩ hlu
  have hbase : l * m ≤ l * b l := mul_le_mul_of_nonneg_left hbl hl.le
  have hu : 0 < u := lt_of_lt_of_le hl hlu
  nlinarith

theorem feedback_lower_bound_upto {b : ℝ → ℝ} {r m : ℝ} (hr : 0 < r)
    (hc : ContinuousOn b (Ici r))
    (hi : ∀ s ∈ Icc r (r + 1), m ≤ b s)
    (hd : ∀ s, r + 1 < s →
      ∃ v, HasDerivAt (fun t => t * b t) v s ∧ b (s - 1) ≤ v)
    (n : ℕ) : ∀ s ∈ Icc r (r + 1 + n), m ≤ b s := by
  induction n with
  | zero => simpa using hi
  | succ n ih =>
    intro s hs
    by_cases hsn : s ≤ r + 1 + n
    · exact ih s ⟨hs.1, hsn⟩
    · have hbase : r + 1 + n < s := lt_of_not_ge hsn
      apply mass_lower_bound (l := r + 1 + n) (by positivity) hbase.le
      · exact hc.mono (fun t ht => by change r ≤ t; linarith [ht.1])
      · exact ih _ ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], le_rfl⟩
      · intro t ht
        obtain ⟨v, hv, hvb⟩ := hd t (by linarith [ht.1, Nat.cast_nonneg (α := ℝ) n])
        refine ⟨v, hv, le_trans (ih (t - 1) ⟨?_, ?_⟩) hvb⟩
        · linarith [ht.1, Nat.cast_nonneg (α := ℝ) n]
        · push_cast at hs
          linarith [ht.2, hs.2]

theorem feedback_lower_bound {b : ℝ → ℝ} {r m : ℝ} (hr : 0 < r)
    (hc : ContinuousOn b (Ici r))
    (hi : ∀ s ∈ Icc r (r + 1), m ≤ b s)
    (hd : ∀ s, r + 1 < s →
      ∃ v, HasDerivAt (fun t => t * b t) v s ∧ b (s - 1) ≤ v)
    {s : ℝ} (hs : r ≤ s) : m ≤ b s := by
  obtain ⟨n, hn⟩ := exists_nat_ge (s - r - 1)
  exact feedback_lower_bound_upto hr hc hi hd n s ⟨hs, by linarith⟩

theorem feedback_not_tendsto_zero {b d : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn b (Ici r)) (hz : b r = 0)
    (hi : ∀ s ∈ Ioc r (r + 1), 0 < b s)
    (hp : ∀ s, r < s → 0 < d s)
    (hd : ∀ s, r + 1 < s →
      HasDerivAt (fun t => t * b t) (b (s - 1) + d (s - 1)) s) :
    ¬ Tendsto b atTop (𝓝 0) := by
  have hder : ∀ s, r + 1 < s →
      ∃ v, HasDerivAt (fun t => t * b t) v s ∧ b (s - 1) ≤ v := by
    intro s hs
    exact ⟨_, hd s hs, by linarith [hp (s - 1) (by linarith)]⟩
  have hn : ∀ s, r ≤ s → 0 ≤ b s := by
    apply fun s hs => feedback_lower_bound hr hc ?_ hder hs
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · simp [← h, hz]
    · exact (hi s ⟨h, hs.2⟩).le
  have hpos : ∀ s ∈ Icc (r + 1) (r + 2), 0 < b s := by
    intro s hs
    have hmono : StrictMonoOn (fun t => t * b t) (Icc (r + 1) s) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (continuousOn_id.mul (hc.mono (by intro t ht; change r ≤ t; linarith [ht.1])))
      intro t ht
      rw [interior_Icc] at ht
      change 0 < deriv (fun t => t * b t) t
      rw [(hd t ht.1).deriv]
      exact add_pos_of_nonneg_of_pos (hn _ (by linarith [ht.1])) (hp _ (by linarith [ht.1]))
    have hmass : (r + 1) * b (r + 1) ≤ s * b s :=
      hmono.monotoneOn ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
    have hfirst : 0 < b (r + 1) := hi _ ⟨by linarith, le_rfl⟩
    have hstart : 0 < (r + 1) * b (r + 1) := mul_pos (by linarith) hfirst
    have hspos : 0 < s := by linarith [hs.1]
    nlinarith
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_forall_le'
    (hc.mono (by intro t ht; change r ≤ t; linarith [ht.1])) hpos
  have htail : ∀ s, r + 1 ≤ s → m ≤ b s := by
    intro s hs
    apply feedback_lower_bound (r := r + 1) (by linarith)
      (hc.mono (by intro t ht; change r ≤ t; exact le_trans (by linarith) ht)) ?_ ?_ hs
    · simpa only [add_assoc, one_add_one_eq_two] using hmin
    · intro t ht
      exact hder t (by linarith)
  intro hlim
  have hevent : ∀ᶠ s in atTop, b s < m := (tendsto_order.mp hlim).2 m hm
  obtain ⟨s, hs, hsm⟩ := (hevent.and (eventually_ge_atTop (r + 1))).exists
  exact (not_lt_of_ge (htail s hsm)) hs

theorem first_zero_of_nonpos {z : ℝ → ℝ} (hc : ContinuousOn z (Ici 1))
    (hi : ∀ s ∈ Icc 1 2, 0 < z s) {S : ℝ} (hS : 1 ≤ S) (hzS : z S ≤ 0) :
    ∃ r, 2 < r ∧ z r = 0 ∧ ∀ s ∈ Ico 1 r, 0 < z s := by
  have h2 : 0 < z 2 := hi _ ⟨by norm_num, le_rfl⟩
  have hS2 : 2 < S := by
    by_contra h
    exact (not_lt_of_ge hzS) (hi S ⟨hS, le_of_not_gt h⟩)
  let Z : Set ℝ := Icc 2 S ∩ z ⁻¹' {0}
  have hcont : ContinuousOn z (Icc 2 S) := hc.mono (by intro t ht; change 1 ≤ t; linarith [ht.1])
  have hcompact : IsCompact Z := isCompact_Icc.of_isClosed_subset
    (hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨t, ht, hzt⟩ := intermediate_value_Icc' hS2.le hcont ⟨hzS, h2.le⟩
  have hne : Z.Nonempty := ⟨t, ht, hzt⟩
  obtain ⟨r, hr⟩ := hcompact.exists_isLeast hne
  have hr2 : 2 ≤ r := hr.1.1.1
  have hrS : r ≤ S := hr.1.1.2
  have hzr : z r = 0 := hr.1.2
  have hr2' : 2 < r := lt_of_le_of_ne hr2 (by intro h; subst r; linarith)
  refine ⟨r, hr2', hzr, ?_⟩
  intro s hs
  by_cases hs2 : s ≤ 2
  · exact hi s ⟨hs.1, hs2⟩
  · by_contra h
    have hz : z s ≤ 0 := le_of_not_gt h
    have hcs : ContinuousOn z (Icc 2 s) := hc.mono (by intro t ht; change 1 ≤ t; linarith [ht.1])
    obtain ⟨t, ht, hzt⟩ := intermediate_value_Icc' (le_of_not_ge hs2) hcs ⟨hz, h2.le⟩
    have htr : r ≤ t := hr.2 ⟨⟨ht.1, by linarith [ht.2, hs.2]⟩, hzt⟩
    linarith [ht.2, hs.2]

theorem no_first_zero {a c : ℝ → ℝ} {r : ℝ} (hr : 2 < r)
    (ha : ContinuousOn a (Ici 1)) (har : a r = 0)
    (hcprev : ∀ s ∈ Ico 1 r, 0 < c s)
    (hsum : ∀ s, 1 ≤ s → 0 < a s + c s)
    (hd : ∀ s, 2 < s → HasDerivAt (fun t => t * a t) (-c (s - 1)) s)
    (hlim : Tendsto a atTop (𝓝 0)) : False := by
  let b : ℝ → ℝ := fun s => -a s
  have hbc : ContinuousOn b (Ici r) := ha.neg.mono (by intro t ht; change 1 ≤ t; exact le_trans (by linarith) ht)
  have hbder : ∀ s, 2 < s → HasDerivAt (fun t => t * b t) (c (s - 1)) s := by
    intro s hs
    convert! (hd s hs).neg using 1 <;> simp [b]
    rfl
  have hbi : ∀ s ∈ Ioc r (r + 1), 0 < b s := by
    intro s hs
    have hm : StrictMonoOn (fun t => t * b t) (Icc r s) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (continuousOn_id.mul (hbc.mono (fun _ ht => ht.1)))
      intro t ht
      rw [interior_Icc] at ht
      change 0 < deriv (fun t => t * b t) t
      rw [(hbder t (by linarith [ht.1])).deriv]
      exact hcprev _ ⟨by linarith [ht.1], by linarith [ht.2, hs.2]⟩
    have hmass := hm ⟨le_rfl, hs.1.le⟩ ⟨hs.1.le, le_rfl⟩ hs.1
    have hbr : b r = 0 := by simp [b, har]
    change r * b r < s * b s at hmass
    rw [hbr, mul_zero] at hmass
    exact (mul_pos_iff_of_pos_left (by linarith [hs.1] : 0 < s)).mp hmass
  apply feedback_not_tendsto_zero (d := fun s => a s + c s) (by linarith) hbc
    (by simp [b, har]) hbi (fun s hs => hsum s (by linarith)) ?_
  · simpa only [b, neg_zero] using hlim.neg
  · intro s hs
    convert! hbder s (by linarith) using 1
    dsimp [b]
    ring

theorem paired_pos {a c : ℝ → ℝ}
    (ha : ContinuousOn a (Ici 1)) (hc : ContinuousOn c (Ici 1))
    (hai : ∀ s ∈ Icc 1 2, 0 < a s) (hci : ∀ s ∈ Icc 1 2, 0 < c s)
    (hsum : ∀ s, 1 ≤ s → 0 < a s + c s)
    (hda : ∀ s, 2 < s → HasDerivAt (fun t => t * a t) (-c (s - 1)) s)
    (hdc : ∀ s, 2 < s → HasDerivAt (fun t => t * c t) (-a (s - 1)) s)
    (hla : Tendsto a atTop (𝓝 0)) (hlc : Tendsto c atTop (𝓝 0)) :
    ∀ s, 1 ≤ s → 0 < a s ∧ 0 < c s := by
  intro S hS
  by_contra h
  have hbad : min (a S) (c S) ≤ 0 := by
    exact le_of_not_gt (fun hpos => h (lt_min_iff.mp hpos))
  obtain ⟨r, hr, hzero, hpre⟩ := first_zero_of_nonpos (ha.inf hc)
    (fun s hs => lt_min (hai s hs) (hci s hs)) hS hbad
  by_cases harc : a r ≤ c r
  · have har : a r = 0 := by simpa only [min_eq_left harc] using hzero
    exact no_first_zero hr ha har (fun s hs => (lt_min_iff.mp (hpre s hs)).2) hsum hda hla
  · have hcr : c r = 0 := by simpa only [min_eq_right (le_of_not_ge harc)] using hzero
    exact no_first_zero hr hc hcr (fun s hs => (lt_min_iff.mp (hpre s hs)).1)
      (fun s hs => by simpa only [add_comm] using hsum s hs) hdc hlc

end NumberTheoryLean.PairedDeficitPositivity

end

end Erdos970

end OAI
