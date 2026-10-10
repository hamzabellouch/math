import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Removal
import OAI.Combinatorics.KMedianRecovery.Strictness.StrictnessGap

namespace OAI

namespace MetricKMedianRecovery

structure RemovalReplay (D X : Type*) [Fintype D] [PseudoMetricSpace X]
    (steps : ℕ) (t K lam : ℝ) where
  location : D → X
  regular : Finset X
  before : Fin steps → Finset X
  after : Fin steps → Finset X
  phase : Fin steps → ℝ
  removal : D → Fin steps
  budget : D → ℝ
  phase_nonneg : ∀ n, 0 ≤ phase n
  before_mono : Monotone before
  after_in_later : ∀ n m, n < m → after n ⊆ before m
  active_threshold : ∀ j f, f ∈ before (removal j) →
    phase (removal j) ≤ t * dist (location j) f
  post_removal : ∀ j, ∃ f ∈ after (removal j),
    t * dist (location j) f ≤ K * phase (removal j)
  final_cap : ∀ j, budget j ≤ K * phase (removal j)
  no_overbid : ∀ n i, i ∈ regular →
    (∑ j, max ((if removal j < n then t * nearestDistance (location j) (before n)
      else phase n) - dist i (location j)) 0) ≤ lam

namespace RemovalReplay

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]
  {steps : ℕ} {t K lam : ℝ} (R : RemovalReplay D X steps t K lam)

noncomputable def boundaryBid (n : Fin steps) (j : D) : ℝ :=
  if R.removal j < n then t * nearestDistance (R.location j) (R.before n)
  else R.phase n

lemma phase_div_le (ht : 0 ≤ t) (htK : t ≤ K) (hK : 0 < K)
    (i : X) (j s : D) (f : X) (hf : f ∈ R.before (R.removal s))
    (b : ℝ) (hb : t * dist (R.location j) f ≤ K * b) :
    R.phase (R.removal s) / K ≤ b + dist i (R.location s) + dist i (R.location j) := by
  have htri : dist (R.location s) f ≤
      dist i (R.location s) + dist i (R.location j) + dist (R.location j) f := by
    calc
      _ ≤ dist (R.location s) i + dist i f := dist_triangle _ _ _
      _ ≤ dist (R.location s) i + (dist i (R.location j) + dist (R.location j) f) :=
        add_le_add_right (dist_triangle _ _ _) _
      _ = _ := by rw [dist_comm (R.location s) i]; ring
  have hmul := mul_le_mul_of_nonneg_left htri ht
  have hds := mul_le_mul_of_nonneg_right htK
    (add_nonneg (dist_nonneg (x := i) (y := R.location s))
      (dist_nonneg (x := i) (y := R.location j)))
  apply (div_le_iff₀ hK).mpr
  nlinarith only [R.active_threshold s f hf, hmul, hds, hb]

lemma earlier_bid_dominates (ht : 0 ≤ t) (htK : t ≤ K) (hK1 : 1 ≤ K)
    (i : X) (j p s : D)
    (hjp : R.removal j ≤ R.removal p) (hps : R.removal p ≤ R.removal s) :
    R.phase (R.removal s) / K - dist i (R.location s) - dist i (R.location j) ≤
      R.boundaryBid (R.removal p) j := by
  classical
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  by_cases hlt : R.removal j < R.removal p
  · obtain ⟨g, hg, _⟩ := R.post_removal j
    have hne : (R.before (R.removal p)).Nonempty :=
      ⟨g, R.after_in_later _ _ hlt hg⟩
    obtain ⟨f, hf, heq⟩ := nearestDistance_attained (R.location j) _ hne
    have hb : 0 ≤ t * nearestDistance (R.location j) (R.before (R.removal p)) :=
      mul_nonneg ht (nearestDistance_nonneg _ _)
    have hconn : t * dist (R.location j) f ≤
        K * (t * nearestDistance (R.location j) (R.before (R.removal p))) := by
      rw [← heq]
      nlinarith only [mul_le_mul_of_nonneg_right hK1 hb]
    have h := R.phase_div_le ht htK hK i j s f (R.before_mono hps hf) _ hconn
    simp only [boundaryBid, hlt, ↓reduceIte]
    linarith only [h]
  · have heq : R.removal j = R.removal p := le_antisymm hjp (le_of_not_gt hlt)
    simp only [boundaryBid, hlt, ↓reduceIte]
    rcases lt_or_eq_of_le hps with hps | hps
    · obtain ⟨f, hf, hb⟩ := R.post_removal j
      have hjs : R.removal j < R.removal s := heq ▸ hps
      have h := R.phase_div_le ht htK hK i j s f (R.after_in_later _ _ hjs hf)
        (R.phase (R.removal j)) hb
      rw [heq] at h
      linarith only [h]
    · have hphase := R.phase_nonneg (R.removal p)
      have hdiv : R.phase (R.removal p) / K ≤ R.phase (R.removal p) := by
        apply (div_le_iff₀ hK).mpr
        nlinarith only [mul_le_mul_of_nonneg_right hK1 hphase]
      rw [← hps]
      linarith only [hdiv, dist_nonneg (x := i) (y := R.location s),
        dist_nonneg (x := i) (y := R.location j)]

lemma selected_no_overbid {q : ℕ} (cluster : Fin q ↪ D) (n : Fin steps)
    (i : X) (hi : i ∈ R.regular) :
    (∑ j, max (R.boundaryBid n (cluster j) - dist i (R.location (cluster j))) 0) ≤ lam := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.map cluster,
        max (R.boundaryBid n j - dist i (R.location j)) 0 :=
      (Finset.sum_map _ _ _).symm
    _ ≤ ∑ j, max (R.boundaryBid n j - dist i (R.location j)) 0 :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => le_max_right _ _
    _ ≤ lam := R.no_overbid n i hi

end RemovalReplay

noncomputable def suffixMaximum {q : ℕ} (a d : Fin q → ℝ) (p : Fin q) : ℝ :=
  (Finset.Ici p).sup' ⟨p, Finset.mem_Ici.mpr le_rfl⟩ (fun s => a s - d s)

lemma le_suffixMaximum {q : ℕ} (a d : Fin q → ℝ) (p s : Fin q) (hps : p ≤ s) :
    a s - d s ≤ suffixMaximum a d p :=
  Finset.le_sup' (fun s => a s - d s) (Finset.mem_Ici.mpr hps)

lemma suffixMaximum_le {q : ℕ} (a d : Fin q → ℝ) (p : Fin q) (b : ℝ)
    (h : ∀ s, p ≤ s → a s - d s ≤ b) : suffixMaximum a d p ≤ b :=
  Finset.sup'_le _ _ (fun s hs => h s (Finset.mem_Ici.mp hs))

theorem replay_bounded_price_strictness
    {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (steps q : ℕ) (hq : 0 < q) (T lam delta v : ℝ)
    (hT : 0 < T) (hlam : 0 ≤ lam) (hdelta : 0 ≤ delta) (hdelta1 : delta < 1)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hvsmall : v ^ 2 ≤ strictnessGap T / (6 * (T + 2)))
    (R : RemovalReplay D X steps (1 - delta) (1 + v ^ 2) lam)
    (i : X) (hi : i ∈ R.regular) (cluster : Fin q ↪ D)
    (horder : Monotone (fun p => R.removal (cluster p)))
    (hP : 0 < ∑ p, dist i (R.location (cluster p)))
    (hprice : lam ≤ T * (∑ p, dist i (R.location (cluster p)))) :
    (∑ p, R.budget (cluster p)) ≤
      lam + (2 - strictnessGap T / 2) * (∑ p, dist i (R.location (cluster p))) := by
  classical
  let K : ℝ := 1 + v ^ 2
  let t : ℝ := 1 - delta
  let d : Fin q → ℝ := fun p => dist i (R.location (cluster p))
  let a : Fin q → ℝ := fun p => R.phase (R.removal (cluster p)) / K
  let A := suffixMaximum a d
  have hK1 : 1 ≤ K := by dsimp [K]; linarith only [sq_nonneg v]
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have ht : 0 ≤ t := by dsimp [t]; linarith only [hdelta1]
  have htK : t ≤ K := by dsimp [t]; linarith only [hdelta, hK1]
  have ha : ∀ p, 0 ≤ a p := fun p => div_nonneg (R.phase_nonneg _) hK.le
  have henv : ∀ p s, p ≤ s → a s - d s ≤ A p := le_suffixMaximum a d
  have hpast : ∀ p j, j < p → A p - 2 * d j ≤
      R.boundaryBid (R.removal (cluster p)) (cluster j) - d j := by
    intro p j hj
    have hmax : A p ≤ R.boundaryBid (R.removal (cluster p)) (cluster j) + d j := by
      apply suffixMaximum_le
      intro s hs
      have h := R.earlier_bid_dominates ht htK hK1 i (cluster j) (cluster p)
        (cluster s) (horder hj.le) (horder hs)
      change a s - d s - d j ≤ _ at h
      linarith only [h]
    linarith only [hmax]
  have hfuture : ∀ p j, p ≤ j → a p - d j ≤
      R.boundaryBid (R.removal (cluster p)) (cluster j) - d j := by
    intro p j hj
    have hnlt : ¬R.removal (cluster j) < R.removal (cluster p) := not_lt.mpr (horder hj)
    change a p - d j ≤ (if _ then _ else _) - d j
    rw [ite_eq_right hnlt]
    have haphase : a p ≤ R.phase (R.removal (cluster p)) := by
      apply (div_le_iff₀ hK).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hK1 (R.phase_nonneg (R.removal (cluster p)))]
    linarith only [haphase]
  have hrow : ∀ p,
      (∑ j ∈ Finset.univ.filter (fun j => p ≤ j), max (a p - d j) 0) +
      (∑ j ∈ Finset.univ.filter (fun j => j < p), max (A p - 2 * d j) 0) ≤ lam := by
    intro p
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply le_trans _ (R.selected_no_overbid cluster (R.removal (cluster p)) i hi)
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j < p
    · simp only [hj, not_le.mpr hj, ↓reduceIte, zero_add]
      exact max_le_max (hpast p j hj) le_rfl
    · simp only [hj, le_of_not_gt hj, ↓reduceIte, add_zero]
      exact max_le_max (hfuture p j (le_of_not_gt hj)) le_rfl
  apply suffix_final_budget_bound q hq T lam (∑ p, d p) v hT hlam hP hprice hv hv1 hvsmall
    d a A (fun p => R.budget (cluster p)) ha (fun _ => dist_nonneg) rfl henv hrow
  intro p
  have hcap := R.final_cap (cluster p)
  change R.budget (cluster p) ≤ K ^ 2 * (R.phase (R.removal (cluster p)) / K)
  have heq : K ^ 2 * (R.phase (R.removal (cluster p)) / K) =
      K * R.phase (R.removal (cluster p)) := by field_simp
  rwa [heq]

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

noncomputable def removalReplay (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam) :
    RemovalReplay D X steps (1 - 3 * v) (1 + v ^ 2) lam where
  location := E.location
  regular := E.regular
  before := fun n => (E.state n).opened
  after := fun n => (E.state (n.val + 1)).opened
  phase := fun n => (E.state n).phase
  removal := E.removal
  budget := (E.state steps).budget
  phase_nonneg := fun n => (E.phase_pos n n.isLt.le).le
  before_mono := fun _ b hab => E.opened_mono hab b.isLt.le
  after_in_later := fun _ b hab => E.opened_mono (Nat.succ_le_of_lt hab) b.isLt.le
  active_threshold := fun j f hf => (E.removal_active j f hf).le
  post_removal := fun j => (E.transition _ (E.removal j).isLt).removal_connection_cap hv1
    (E.phase_pos _ (E.removal j).isLt.le).le j (E.removal_inactive j)
  final_cap := E.final_cap
  no_overbid := by
    intro n i hi
    convert E.no_overbid hv hv1 hlam n n.isLt.le i hi using 1
    unfold bidRow
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    by_cases hj : E.removal j < n
    · rw [ite_eq_left hj]
      exact (clippedAt_of_inactive E.location (1 - 3 * v) (E.state n).phase
        (E.state n).opened j (by linarith only [hv1])
        (fun h => not_le_of_gt hj ((E.active_iff_before_removal n n.isLt.le j).mp h))).symm
    · rw [ite_eq_right hj]
      exact (clippedAt_of_active E.location (1 - 3 * v) (E.state n).phase
        (E.state n).opened j (by linarith only [hv1])
        ((E.active_iff_before_removal n n.isLt.le j).mpr (le_of_not_gt hj))).symm

end ValidExecution

theorem valid_execution_bounded_price_strictness
    {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {steps q : ℕ} (v lam eta T : ℝ)
    (E : ValidExecution D X steps v lam eta) (cluster : Fin q ↪ D) (i : X)
    (hq : 0 < q) (hi : i ∈ E.regular)
    (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam) (hT : 0 < T)
    (hP : 0 < ∑ j, dist i (E.location (cluster j)))
    (hprice : lam ≤ T * ∑ j, dist i (E.location (cluster j)))
    (hsmall : v ^ 2 ≤ ((1 / (200 * (T + 2))) ^ 2 / 100) / (6 * (T + 2))) :
    (∑ j, (E.state steps).budget (cluster j)) ≤
      lam + (2 - ((1 / (200 * (T + 2))) ^ 2 / 100) / 2) *
        ∑ j, dist i (E.location (cluster j)) := by
  classical
  let R := E.removalReplay hv hv1 hlam
  let σ := Tuple.sort (fun j => R.removal (cluster j))
  let selected : Fin q ↪ D := σ.toEmbedding.trans cluster
  have horder : Monotone (fun j => R.removal (selected j)) :=
    Tuple.monotone_sort (fun j => R.removal (cluster j))
  have hcost : (∑ j, dist i (R.location (selected j))) =
      ∑ j, dist i (E.location (cluster j)) := by
    change (∑ j, (fun k => dist i (E.location (cluster k))) (σ j)) = _
    exact Equiv.sum_comp σ (fun k : Fin q => dist i (E.location (cluster k)))
  have hbudget : (∑ j, R.budget (selected j)) =
      ∑ j, (E.state steps).budget (cluster j) := by
    change (∑ j, (fun k => (E.state steps).budget (cluster k)) (σ j)) = _
    exact Equiv.sum_comp σ (fun k : Fin q => (E.state steps).budget (cluster k))
  have hgap : v ^ 2 ≤ strictnessGap T / (6 * (T + 2)) := hsmall
  have hbound := replay_bounded_price_strictness steps q hq T lam (3 * v) v hT hlam.le
    (by linarith only [hv]) (by linarith only [hv1]) hv (by linarith only [hv1])
    hgap R i hi selected horder (hcost ▸ hP) (hcost ▸ hprice)
  rw [hbudget, hcost] at hbound
  exact hbound

end MetricKMedianRecovery

end OAI
