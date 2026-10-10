import Mathlib

namespace OAI

namespace MetricKMedianRecovery

noncomputable def nearestDistance {X : Type*} [PseudoMetricSpace X]
    (x : X) (S : Finset X) : ℝ :=
  if h : S.Nonempty then S.inf' h (dist x) else 0

def activeAt {D X : Type*} [PseudoMetricSpace X] (loc : D → X)
    (t z : ℝ) (Q : Finset X) (j : D) : Prop :=
  ∀ f ∈ Q, z < t * dist (loc j) f

noncomputable def clippedAt {D X : Type*} [PseudoMetricSpace X] (loc : D → X)
    (t z : ℝ) (Q : Finset X) (j : D) : ℝ :=
  if Q.Nonempty then min z (t * nearestDistance (loc j) Q) else z

noncomputable def bidRow {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) : ℝ :=
  ∑ j, max (clippedAt loc t z Q j - dist i (loc j)) 0

def admissibleBids {D X : Type*} [PseudoMetricSpace X] (loc : D → X)
    (t K v z : ℝ) (Q : Finset X) (i : X) (tau : D → ℝ) : Prop :=
  ∀ j, activeAt loc t z Q j →
    z ≤ tau j ∧ tau j ≤ K * z ∧ (∀ f ∈ Q, tau j ≤ t * dist (loc j) f) ∧
      (v * z < dist i (loc j) → tau j = z)

noncomputable def openingPayment {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) (tau : D → ℝ) : ℝ := by
  classical
  exact ∑ j, max ((if activeAt loc t z Q j then tau j
    else t * nearestDistance (loc j) Q) - t * dist i (loc j)) 0

noncomputable def openingDual {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i₀ : X) (tau : D → ℝ) (a : D) : ℝ := by
  classical
  exact ∑ j, if activeAt loc t z Q j then max (tau j - dist i₀ (loc j)) 0
    else max (tau a - 2 * dist i₀ (loc j) - dist i₀ (loc a)) 0

def etaOpenable {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ) (i : X) : Prop :=
  ∃ tau : D → ℝ, admissibleBids loc t K v z Q i tau ∧
    lam - (Fintype.card D : ℝ) * eta ≤ openingPayment loc t z Q i tau ∧
    ∀ i₀ ∈ F, ∀ a, activeAt loc t z Q a → openingDual loc t z Q i₀ tau a ≤ lam

lemma nearestDistance_nonneg {X : Type*} [PseudoMetricSpace X]
    (x : X) (S : Finset X) : 0 ≤ nearestDistance x S := by
  classical
  unfold nearestDistance
  split_ifs with h
  · exact Finset.le_inf' h _ (fun _ _ => dist_nonneg)
  · exact le_rfl

lemma nearestDistance_attained {X : Type*} [PseudoMetricSpace X]
    (x : X) (S : Finset X) (hS : S.Nonempty) :
    ∃ f ∈ S, nearestDistance x S = dist x f := by
  classical
  simpa [nearestDistance, hS] using Finset.exists_mem_eq_inf' hS (dist x)

lemma nearestDistance_le_mem {X : Type*} [PseudoMetricSpace X]
    (x : X) (S : Finset X) (f : X) (hf : f ∈ S) : nearestDistance x S ≤ dist x f := by
  classical
  have hS : S.Nonempty := ⟨f, hf⟩
  rw [nearestDistance, dite_eq_left hS]
  exact Finset.inf'_le (dist x) hf

lemma nearestDistance_antitone {X : Type*} [PseudoMetricSpace X]
    (x : X) (S W : Finset X) (hS : S.Nonempty) (hSW : S ⊆ W) :
    nearestDistance x W ≤ nearestDistance x S := by
  obtain ⟨f, hf, heq⟩ := nearestDistance_attained x S hS
  rw [heq]
  exact nearestDistance_le_mem x W f (hSW hf)

lemma activeAt_iff {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D)
    (ht : 0 ≤ t) (hQ : Q.Nonempty) :
    activeAt loc t z Q j ↔ z < t * nearestDistance (loc j) Q := by
  constructor
  · intro h
    obtain ⟨f, hf, heq⟩ := nearestDistance_attained (loc j) Q hQ
    rw [heq]
    exact h f hf
  · intro h f hf
    exact h.trans_le (mul_le_mul_of_nonneg_left (nearestDistance_le_mem _ _ _ hf) ht)

lemma inactive_nonempty {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D)
    (h : ¬activeAt loc t z Q j) : Q.Nonempty := by
  by_contra hQ
  apply h
  intro f hf
  exact (hQ ⟨f, hf⟩).elim

lemma clippedAt_of_active {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D)
    (ht : 0 ≤ t) (h : activeAt loc t z Q j) : clippedAt loc t z Q j = z := by
  classical
  unfold clippedAt
  split_ifs with hQ
  · exact min_eq_left ((activeAt_iff loc t z Q j ht hQ).mp h).le
  · rfl

lemma clippedAt_of_inactive {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D)
    (ht : 0 ≤ t) (h : ¬activeAt loc t z Q j) :
    clippedAt loc t z Q j = t * nearestDistance (loc j) Q := by
  classical
  have hQ := inactive_nonempty loc t z Q j h
  have hc : t * nearestDistance (loc j) Q ≤ z := by
    exact not_lt.mp (fun hh => h ((activeAt_iff loc t z Q j ht hQ).mpr hh))
  simp [clippedAt, hQ, min_eq_right hc]

lemma clippedAt_le_phase {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D) : clippedAt loc t z Q j ≤ z := by
  classical
  unfold clippedAt
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

lemma clippedAt_le_connection {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D) (f : X) (hf : f ∈ Q)
    (ht : 0 ≤ t) : clippedAt loc t z Q j ≤ t * dist (loc j) f := by
  classical
  have hQ : Q.Nonempty := ⟨f, hf⟩
  calc
    _ = min z (t * nearestDistance (loc j) Q) := by simp only [clippedAt, hQ, ↓reduceIte]
    _ ≤ t * nearestDistance (loc j) Q := min_le_right _ _
    _ ≤ t * dist (loc j) f := mul_le_mul_of_nonneg_left (nearestDistance_le_mem _ _ _ hf) ht

lemma clippedAt_mono_phase {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (Q : Finset X) (j : D) :
    Monotone (fun z => clippedAt loc t z Q j) := by
  classical
  intro z w hzw
  unfold clippedAt
  split_ifs
  · exact min_le_min hzw le_rfl
  · exact hzw

lemma clippedAt_antitone_open {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q W : Finset X) (j : D) (ht : 0 ≤ t) (hQW : Q ⊆ W) :
    clippedAt loc t z W j ≤ clippedAt loc t z Q j := by
  classical
  by_cases hQ : Q.Nonempty
  · have hW : W.Nonempty := hQ.mono hQW
    simp only [clippedAt, hQ, hW, ↓reduceIte]
    exact min_le_min le_rfl (mul_le_mul_of_nonneg_left (nearestDistance_antitone _ _ _ hQ hQW) ht)
  · simpa [clippedAt, hQ] using clippedAt_le_phase loc t z W j

lemma bidRow_antitone_open {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q W : Finset X) (i : X) (ht : 0 ≤ t) (hQW : Q ⊆ W) :
    bidRow loc t z W i ≤ bidRow loc t z Q i := by
  apply Finset.sum_le_sum
  intro j _
  exact max_le_max (sub_le_sub_right (clippedAt_antitone_open loc t z Q W j ht hQW) _) le_rfl

lemma continuous_clippedAt {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (Q : Finset X) (j : D) :
    Continuous (fun z => clippedAt loc t z Q j) := by
  classical
  unfold clippedAt
  split_ifs
  · exact continuous_id.min continuous_const
  · exact continuous_id

lemma continuous_bidRow {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (Q : Finset X) (i : X) :
    Continuous (fun z => bidRow loc t z Q i) := by
  apply continuous_finsetSum
  intro j _
  exact ((continuous_clippedAt loc t Q j).sub continuous_const).max continuous_const

lemma bidRow_eq_zero_of_open {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) (hi : i ∈ Q)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : bidRow loc t z Q i = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have h := clippedAt_le_connection loc t z Q j i hi ht
  have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x := loc j) (y := i))
  rw [dist_comm (loc j) i] at h hd
  apply max_eq_right
  nlinarith only [h, hd]

lemma inactive_at_later_phase {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z y : ℝ) (Q : Finset X) (j : D)
    (hzy : z ≤ y) (h : ¬activeAt loc t z Q j) : ¬activeAt loc t y Q j := by
  intro hy
  apply h
  intro f hf
  exact lt_of_le_of_lt hzy (hy f hf)

lemma capped_triangle_row {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t u : ℝ) (Q : Finset X) (i : X) (a j : D)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hQ : Q.Nonempty)
    (hcap : ∀ f ∈ Q, u ≤ t * dist (loc a) f) :
    u - 2 * dist i (loc j) - dist i (loc a) ≤
      t * nearestDistance (loc j) Q - dist i (loc j) := by
  obtain ⟨f, hf, heq⟩ := nearestDistance_attained (loc j) Q hQ
  have htri : dist (loc a) f ≤ dist i (loc a) + dist i (loc j) + dist (loc j) f := by
    calc
      _ ≤ dist (loc a) i + dist i f := dist_triangle _ _ _
      _ ≤ dist (loc a) i + (dist i (loc j) + dist (loc j) f) :=
        add_le_add_right (dist_triangle _ _ _) _
      _ = _ := by rw [dist_comm (loc a) i]; ring
  have hm := mul_le_mul_of_nonneg_left htri ht
  have hd := mul_le_mul_of_nonneg_right ht1
    (add_nonneg (dist_nonneg (x := i) (y := loc a)) (dist_nonneg (x := i) (y := loc j)))
  rw [heq]
  nlinarith only [hcap f hf, hm, hd]

theorem crossing_openable {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (F Q : Finset X) (v z y lam : ℝ) (i : X)
    (hv : 0 < v) (hvsmall : v < 1 / 6) (hz : 0 < z)
    (hzy : z ≤ y) (hyK : y ≤ (1 + v ^ 2) * z)
    (heq : bidRow loc (1 - 3 * v) y Q i = lam)
    (hrows : ∀ i₀ ∈ F, bidRow loc (1 - 3 * v) y Q i₀ ≤ lam) :
    etaOpenable loc F Q (1 - 3 * v) (1 + v ^ 2) v z lam 0 i := by
  classical
  let t : ℝ := 1 - 3 * v
  let tau : D → ℝ := fun j => if dist i (loc j) ≤ v * z then clippedAt loc t y Q j else z
  have ht : 0 ≤ t := by dsimp [t]; linarith only [hvsmall]
  have ht1 : t ≤ 1 := by dsimp [t]; linarith only [hv]
  have hKz : z ≤ (1 + v ^ 2) * z := hzy.trans hyK
  have hactiveLow : ∀ j, activeAt loc t z Q j → z ≤ clippedAt loc t y Q j := by
    intro j hj
    have h := clippedAt_mono_phase loc t Q j hzy
    change clippedAt loc t z Q j ≤ clippedAt loc t y Q j at h
    rwa [clippedAt_of_active loc t z Q j ht hj] at h
  have hadm : admissibleBids loc t (1 + v ^ 2) v z Q i tau := by
    intro j hj
    constructor
    · dsimp [tau]
      split_ifs
      · exact hactiveLow j hj
      · exact le_rfl
    constructor
    · dsimp [tau]
      split_ifs
      · exact (clippedAt_le_phase loc t y Q j).trans hyK
      · exact hKz
    constructor
    · intro f hf
      dsimp [tau]
      split_ifs
      · exact clippedAt_le_connection loc t y Q j f hf ht
      · exact (hj f hf).le
    · intro hfar
      simp [tau, not_le.mpr hfar]
  have htau : ∀ j, activeAt loc t z Q j → tau j ≤ clippedAt loc t y Q j := by
    intro j hj
    dsimp [tau]
    split_ifs
    · exact le_rfl
    · exact hactiveLow j hj
  have hpay : bidRow loc t y Q i ≤ openingPayment loc t z Q i tau := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : activeAt loc t z Q j
    · simp only [hj, ↓reduceIte]
      apply max_le_max _ le_rfl
      dsimp [tau]
      split_ifs with hnear
      · have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x := i) (y := loc j))
        nlinarith only [hd]
      · have hfar : v * z ≤ dist i (loc j) := le_of_lt (not_le.mp hnear)
        have hm := mul_le_mul_of_nonneg_left hfar (by positivity : 0 ≤ 3 * v)
        have hvz : 0 ≤ v ^ 2 * z := mul_nonneg (sq_nonneg v) hz.le
        have hclip := (clippedAt_le_phase loc t y Q j).trans hyK
        dsimp [t]
        nlinarith only [hm, hvz, hclip]
    · simp only [hj, ↓reduceIte]
      rw [clippedAt_of_inactive loc t y Q j ht (inactive_at_later_phase loc t z y Q j hzy hj)]
      apply max_le_max _ le_rfl
      have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x := i) (y := loc j))
      nlinarith only [hd]
  refine ⟨tau, hadm, ?_, ?_⟩
  · simpa [← heq, t] using hpay
  · intro i₀ hi₀ a ha
    change openingDual loc t z Q i₀ tau a ≤ lam
    have htarget : bidRow loc t y Q i₀ ≤ lam := hrows i₀ hi₀
    apply le_trans _ htarget
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : activeAt loc t z Q j
    · simp only [hj, ↓reduceIte]
      exact max_le_max (sub_le_sub_right (htau j hj) _) le_rfl
    · simp only [hj, ↓reduceIte]
      rw [clippedAt_of_inactive loc t y Q j ht (inactive_at_later_phase loc t z y Q j hzy hj)]
      exact max_le_max (capped_triangle_row loc t (tau a) Q i₀ a j ht ht1
        (inactive_nonempty loc t z Q j hj) (hadm a ha).2.2.1) le_rfl

end MetricKMedianRecovery

end OAI
