import OAI.Combinatorics.BalancedRyser.Selection.SelectionOccupancyBound

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process
open FiniteHistory
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

omit [Fintype I] in
theorem positive_snapshot_surviving_update (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) (S' : State I V) (hout : out.1 = some S')
    (hpos : 0 < snapshotWeight p q t G before out) :
    ∃ S r, before.1 = some S ∧ out.2 = some r ∧
      update G S r.1 r.2.1 r.2.2 = S' := by
  obtain ⟨S, r, hb, hr, _⟩ := positive_snapshot_survival_before p q t G before out
    (by rw [hout]; simp) hpos
  refine ⟨S, r, hb, hr, ?_⟩
  have hcons : out.1 = advance q G before.1 out.2 := by
    by_contra hn
    simp [snapshotWeight, hn] at hpos
  rw [hout, hb, hr] at hcons
  change some S' = (if Postcheck q G S r.2.1 r.2.2 then
    some (update G S r.1 r.2.1 r.2.2) else none) at hcons
  split at hcons
  · exact (Option.some.inj hcons).symm
  · contradiction

theorem recorded_seen_on_support_path (p : Parameters) (q : ℕ) (G : Input I V)
    (ω : Path (Snapshot I V)) (hi : ω 0 = initialSnapshot)
    (hsupport : ∀ j, snapshotPMF p q j G (ω j) (ω (j + 1)) ≠ 0) :
    ∀ t S, (ω t).1 = some S → ∀ i v, S.recorded i = some v →
      ∃ j < t, ∃ r : Noise I V, (ω (j + 1)).2 = some r ∧ r.2.1 = v := by
  intro t
  induction t with
  | zero =>
    intro S hS i v hv
    have hinit : S = initialState := by
      simpa [hi, initialSnapshot] using hS.symm
    simp [hinit, initialState] at hv
  | succ t ih =>
    intro S' hS' i v hv
    have hp : 0 < snapshotWeight p q t G (ω t) (ω (t + 1)) := by
      have hn : snapshotWeight p q t G (ω t) (ω (t + 1)) ≠ 0 := by
        intro hz
        apply hsupport t
        change ENNReal.ofReal (snapshotWeight p q t G (ω t) (ω (t + 1))) = 0
        rw [hz, ENNReal.ofReal_zero]
      exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G _ _) (Ne.symm hn)
    obtain ⟨S, r, hb, hr, hu⟩ :=
      positive_snapshot_surviving_update p q t G _ _ S' hS' hp
    rw [← hu] at hv
    by_cases heq : i = r.1
    · subst i
      have hv' : r.2.1 = v := by simpa [update] using hv
      exact ⟨t, by omega, r, hr, hv'⟩
    · have hv' : S.recorded i = some v := by simpa [update, heq] using hv
      obtain ⟨j, hj, s, hs, hsv⟩ := ih S hb i v hv'
      exact ⟨j, by omega, s, hs, hsv⟩

theorem ae_occupancyPrefix_avoids_recorded (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S →
      ∀ x ∈ occupancyPrefix q A line l T t (frestrictLe t ω),
      ∀ i v, S.recorded i = some v → ¬ (line v ≠ l ∧ A.incident x (line v)) := by
  filter_upwards [ae_initial_state (fun n => snapshotPMF p q n G) initialSnapshot,
    ae_all_iff.2 (fun n => ae_step_support (fun j => snapshotPMF p q j G)
      initialSnapshot n)] with ω hi hs
  intro t S hS x hx i v hv
  obtain ⟨j, hj, r, hr, hrv⟩ := recorded_seen_on_support_path p q G ω hi hs t S hS i v hv
  have hx' := (Finset.mem_filter.mp hx).2 j hj r hr
  simpa [hrv] using hx'

omit [Fintype V] in
theorem remaining_lines_loss_le (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (l : L) (R : Finset P) (hR : ∀ x ∈ R, A.incident x l)
    (J : Finset I) (a : I → V) :
    R.card ≤ (R.filter (fun x => ∀ i ∈ J,
      ¬ (line (a i) ≠ l ∧ A.incident x (line (a i))))).card + J.card := by
  classical
  let bad : Finset P := J.biUnion (fun i => R.filter
    (fun x => line (a i) ≠ l ∧ A.incident x (line (a i))))
  have hbad : bad.card ≤ J.card := by
    simpa only [mul_one] using Finset.card_biUnion_le_card_mul J
      (fun i => R.filter (fun x => line (a i) ≠ l ∧ A.incident x (line (a i)))) 1
      (fun i _ => SelectionOccupancy.plane_deletion_card_le_one A R l (line (a i)) hR)
  have heq : R.filter (fun x => ∀ i ∈ J,
      ¬ (line (a i) ≠ l ∧ A.incident x (line (a i)))) = R \ bad := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, bad, Finset.mem_biUnion]
    aesop
  rw [heq]
  have hsub : bad ⊆ R := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxi).1
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  omega

omit [Fintype V] in
theorem finalTracked_loss_le_remaining (q : ℕ) (_ : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P)
    (l : L) (R : Finset P) (hRT : R ⊆ T l) (hR : ∀ x ∈ R, A.incident x l)
    (S : State I V) (a : I → V)
    (hext : ∀ i, i ∉ S.remaining → S.recorded i = some (a i))
    (havoid : ∀ x ∈ R, ∀ i v, S.recorded i = some v →
      ¬ (line v ≠ l ∧ A.incident x (line v))) :
    R.card ≤ (Selection.finalTracked A line T a l).card + S.remaining.card := by
  have hc := remaining_lines_loss_le q A line l R hR S.remaining a
  apply hc.trans
  apply Nat.add_le_add_right
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxR, hxgood⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hRT hxR, ?_⟩
  intro i hneq hinc
  by_cases hi : i ∈ S.remaining
  · exact hxgood i hi ⟨hneq, hinc⟩
  · exact havoid x hxR i (a i) (hext i hi) ⟨hneq, hinc⟩

theorem ae_completed_occupancy_loss (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P)
    (hT : ∀ l x, x ∈ T l → A.incident x l) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S → ∀ a : I → V,
      (∀ i, i ∉ S.remaining → S.recorded i = some (a i)) → ∀ l,
      (occupancyPrefix q A line l (T l) t (frestrictLe t ω)).card ≤
        (Selection.finalTracked A line T a l).card + S.remaining.card := by
  have hall := ae_all_iff.2 (fun l =>
    ae_occupancyPrefix_avoids_recorded p q G A line l (T l))
  filter_upwards [hall] with ω hω
  intro t S hS a hext l
  exact finalTracked_loss_le_remaining q G A line T l _
    (occupancyPrefix_subset q A line l (T l) t _)
    (fun x hx => hT l x (occupancyPrefix_subset q A line l (T l) t _ hx))
    S a hext (hω l t S hS)

def recordedTracked (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (T : L → Finset P) (S : State I V) (l : L) : Finset P :=
  (T l).filter (fun x => ∀ i v, S.recorded i = some v →
    ¬ (line v ≠ l ∧ A.incident x (line v)))

theorem ae_occupancyPrefix_subset_recorded (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S → ∀ l,
      occupancyPrefix q A line l (T l) t (frestrictLe t ω) ⊆ recordedTracked q A line T S l := by
  filter_upwards [ae_all_iff.2 (fun l =>
    ae_occupancyPrefix_avoids_recorded p q G A line l (T l))] with ω hω
  intro t S hS l x hx
  exact Finset.mem_filter.mpr ⟨occupancyPrefix_subset q A line l (T l) t _ hx,
    hω l t S hS x hx⟩

theorem surviving_recorded_occupancy_bound (p : Parameters) (hp : p.Admissible)
    (q : ℕ) (hq : 0 < q) (hPq : 2 * p.Pstar ≤ q) (hBq : 2 * p.Bstar ≤ q)
    (G : Input I V) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (T : L → Finset P)
    (hT : ∀ l x, x ∈ T l → A.incident x l)
    (hcard : ∀ l, p.c₀ * q ≤ ((T l).card : ℝ)) (t : ℕ) (ht : t ≤ 3 * q) :
    (snapshotPathLaw p q G).real {ω | ∃ S, (ω t).1 = some S ∧ ∃ l,
      ((recordedTracked q A line T S l).card : ℝ) ≤ 2 * p.rho * q} ≤
      2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
  refine le_trans ?_ (surviving_all_line_occupancy_bound p hp q hq hPq hBq G A
    index line hline T hT hcard t ht)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_occupancyPrefix_subset_recorded p q G A line T] with ω hω hbad
  obtain ⟨S, hS, l, hl⟩ := hbad
  refine ⟨by rw [hS]; simp, l, ?_⟩
  exact le_trans (by exact_mod_cast Finset.card_le_card (hω t S hS l)) hl

theorem recorded_finalTracked_loss_le (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P)
    (hT : ∀ l x, x ∈ T l → A.incident x l) (S : State I V) (a : I → V)
    (hext : ∀ i, i ∉ S.remaining → S.recorded i = some (a i)) (l : L) :
    (recordedTracked q A line T S l).card ≤
      (Selection.finalTracked A line T a l).card + S.remaining.card := by
  exact finalTracked_loss_le_remaining q G A line T l _ (Finset.filter_subset _ _)
    (fun x hx => hT l x (Finset.mem_filter.mp hx).1) S a hext
    (fun x hx => (Finset.mem_filter.mp hx).2)

theorem completion_occupancyMass_le_bad_recorded (p : Parameters) (q : ℕ)
    (G : Input I V) (A : FiniteAffine.Plane q P D L) (line : V → L)
    (T : L → Finset P) (hT : ∀ l x, x ∈ T l → A.incident x l)
    (S : State I V) (law : Selection.OutputLaw G)
    (hrem : (S.remaining.card : ℝ) ≤ p.rho * q)
    (hext : ∀ a, 0 < law.weight a → ∀ i, i ∉ S.remaining →
      S.recorded i = some (a i)) :
    Selection.occupancyFailureMass law A line T p.rho ≤
      if ∃ l, ((recordedTracked q A line T S l).card : ℝ) ≤ 2 * p.rho * q
        then 1 else 0 := by
  classical
  split
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => law.nonnegative a)).trans law.mass_le_one
  · rename_i hgood
    unfold Selection.occupancyFailureMass
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro a ha
    apply le_antisymm _ (law.nonnegative a)
    apply le_of_not_gt
    intro hpos
    obtain ⟨l, hl⟩ := (Finset.mem_filter.mp ha).2
    have hlower : 2 * p.rho * (q : ℝ) < (recordedTracked q A line T S l).card :=
      lt_of_not_ge (fun h => hgood ⟨l, h⟩)
    have hloss := recorded_finalTracked_loss_le q G A line T hT S a (hext a hpos) l
    have hlossR : ((recordedTracked q A line T S l).card : ℝ) ≤
        (Selection.finalTracked A line T a l).card + (S.remaining.card : ℝ) := by
      exact_mod_cast hloss
    linarith

end Balanced.Selection.Process

end

end OAI
