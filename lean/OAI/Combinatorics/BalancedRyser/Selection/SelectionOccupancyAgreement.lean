import OAI.Combinatorics.BalancedRyser.Probability.FiniteHistoryInvariant
import OAI.Combinatorics.BalancedRyser.Selection.SelectionOccupancyTrack

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
theorem positive_snapshot_survival_before (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) (hout : out.1 ≠ none)
    (hpos : 0 < snapshotWeight p q t G before out) :
    ∃ S r, before.1 = some S ∧ out.2 = some r ∧ Precheck p q t G S := by
  unfold snapshotWeight at hpos
  split at hpos
  next hcons =>
    cases hb : before.1 with
    | none => exact (hout (by simpa [advance, hb] using hcons)).elim
    | some S =>
      cases hr : out.2 with
      | none => exact (hout (by simpa [advance, hb, hr] using hcons)).elim
      | some r =>
        refine ⟨S, r, rfl, rfl, ?_⟩
        by_contra hpre
        simp [drawStepWeight, hb, hr, hpre] at hpos
  next => exact (lt_irrefl 0 hpos).elim

theorem occupancyPrefix_succ_of_draw (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (l : L) (T : Finset P) (t : ℕ)
    (ω : Path (Snapshot I V)) (r : Noise I V) (hr : (ω (t + 1)).2 = some r) :
    occupancyPrefix q A line l T (t + 1) (frestrictLe (t + 1) ω) =
      SelectionOccupancy.afterPlaneLine A
        (occupancyPrefix q A line l T t (frestrictLe t ω)) l (line r.2.1) := by
  ext x
  simp only [occupancyPrefix, SelectionOccupancy.afterPlaneLine, Finset.mem_filter]
  constructor
  · rintro ⟨hx, havoid⟩
    refine ⟨⟨hx, ?_⟩, ?_⟩
    · intro j hj s hs
      exact havoid j (by omega) s hs
    · exact havoid t (by omega) r hr
  · rintro ⟨⟨hx, havoid⟩, hlast⟩
    refine ⟨hx, ?_⟩
    intro j hj s hs
    by_cases hlt : j < t
    · exact havoid j hlt s hs
    · have heq : j = t := by omega
      subst j
      have hrs : r = s := Option.some.inj (hr.symm.trans hs)
      simpa [← hrs] using hlast

theorem occupancyTrack_eq_on_surviving_path (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P)
    (ω : Path (Snapshot I V))
    (hsupport : ∀ j, snapshotPMF p q j G (ω j) (ω (j + 1)) ≠ 0) :
    ∀ t, (ω t).1 ≠ none →
      occupancyTrack p q G A line l T t ω =
        ((occupancyPrefix q A line l T t (frestrictLe t ω)).card : ℝ) /
          (1 - p.Bstar / q) ^ t := by
  intro t
  induction t with
  | zero => intro _; simp [occupancyTrack]
  | succ t ih =>
    intro hsurv
    have hp : 0 < snapshotWeight p q t G (ω t) (ω (t + 1)) := by
      have hn : snapshotWeight p q t G (ω t) (ω (t + 1)) ≠ 0 := by
        intro hz
        apply hsupport t
        change ENNReal.ofReal (snapshotWeight p q t G (ω t) (ω (t + 1))) = 0
        rw [hz, ENNReal.ofReal_zero]
      exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G _ _) (Ne.symm hn)
    obtain ⟨S, r, hb, hr, hpre⟩ :=
      positive_snapshot_survival_before p q t G (ω t) (ω (t + 1)) hsurv hp
    have hprev := ih (by rw [hb]; simp)
    have hinc := additiveTrack_increment (T.card : ℝ)
      (occupancyResponse p q G A line l T) t ω
    change occupancyTrack p q G A line l T (t + 1) ω -
      occupancyTrack p q G A line l T t ω = _ at hinc
    have hlast : (frestrictLe t ω ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1 = some S := hb
    simp only [stepObservable, occupancyResponse, hlast, hr, hpre, ite_true] at hinc
    rw [occupancyPrefix_succ_of_draw q A line l T t ω r hr]
    linarith

theorem ae_occupancyTrack_eq (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t, (ω t).1 ≠ none →
      occupancyTrack p q G A line l T t ω =
        ((occupancyPrefix q A line l T t (frestrictLe t ω)).card : ℝ) /
          (1 - p.Bstar / q) ^ t := by
  have hs := ae_all_iff.2 (fun j => FiniteHistory.ae_step_support
    (fun n => snapshotPMF p q n G) (initialSnapshot (I := I) (V := V)) j)
  filter_upwards [hs] with ω hω
  exact occupancyTrack_eq_on_surviving_path p q G A line l T ω hω

theorem surviving_occupancy_lower_tail (p : Parameters) (q N : ℕ) (G : Input I V)
    (hc : 0 < p.c) (hq : 0 < q) (hN : 1 ≤ N)
    (hscale : ∀ j < N, p.smin ≤ p.sizeScale q j)
    (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) (d : ℝ) (hd : 0 < d)
    (hdenom : ∀ j < N, d ≤ (1 - p.Bstar / q) ^ (j + 1))
    (u : ℝ) (hu : 0 < u) (hub : u ≤ (T.card : ℝ))
    (t : ℕ) (ht : t ≤ N) (hdt : d ≤ (1 - p.Bstar / q) ^ t) :
    (snapshotPathLaw p q G).real {ω | (ω t).1 ≠ none ∧
      ((occupancyPrefix q A line l T t (frestrictLe t ω)).card : ℝ) ≤
        d * ((T.card : ℝ) - u)} ≤
      2 * Real.exp (-u ^ 2 / (8 * (N : ℝ) * ((1 + p.Bstar) / d) ^ 2)) := by
  refine le_trans ?_ (occupancyTrack_lower_tail p q N G hc hq hN hscale hfactor
    A index line hline l T hT d hd hdenom u hu t ht)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_occupancyTrack_eq p q G A line l T] with ω hω hbad
  rcases hbad with ⟨hsurv, hsmall⟩
  rw [hω t hsurv]
  apply (div_le_iff₀ (pow_pos hfactor t)).2
  exact hsmall.trans (by nlinarith [mul_le_mul_of_nonneg_right hdt (sub_nonneg.mpr hub)])

end Balanced.Selection.Process

end

end OAI
