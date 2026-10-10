import OAI.Combinatorics.BalancedRyser.Probability.FiniteHistoryAdditive
import OAI.Combinatorics.BalancedRyser.Selection.SelectionHistory
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessOccupancy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

open FiniteHistory
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

def occupancyPrefix (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (l : L) (T : Finset P) (t : ℕ)
    (h : Prefix (Snapshot I V) t) : Finset P :=
  T.filter (fun x => ∀ (j : ℕ) (hj : j < t),
    ∀ r, (h ⟨j + 1, Finset.mem_Iic.mpr (by omega)⟩).2 = some r →
      ¬ (line r.2.1 ≠ l ∧ A.incident x (line r.2.1)))

theorem occupancyPrefix_subset (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (l : L) (T : Finset P) (t : ℕ)
    (h : Prefix (Snapshot I V) t) : occupancyPrefix q A line l T t h ⊆ T :=
  Finset.filter_subset _ _

@[simp] theorem occupancyPrefix_zero (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (l : L) (T : Finset P) (h : Prefix (Snapshot I V) 0) :
    occupancyPrefix q A line l T 0 h = T := by simp [occupancyPrefix]

def occupancyResponse (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P)
    (t : ℕ) (h : Prefix (Snapshot I V) t) (out : Snapshot I V) : ℝ :=
  match (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1, out.2 with
  | some S, some r => if Precheck p q t G S then
      ((SelectionOccupancy.afterPlaneLine A (occupancyPrefix q A line l T t h)
        l (line r.2.1)).card : ℝ) / (1 - p.Bstar / q) ^ (t + 1) -
      ((occupancyPrefix q A line l T t h).card : ℝ) / (1 - p.Bstar / q) ^ t
    else 0
  | _, _ => 0

def occupancyTrack (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P) :
    ℕ → Path (Snapshot I V) → ℝ :=
  additiveTrack (T.card : ℝ) (occupancyResponse p q G A line l T)

theorem occupancyResponse_bound (p : Parameters) (q t : ℕ) (G : Input I V)
    (hc : 0 < p.c) (hq : 0 < q) (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) (d : ℝ) (hd : 0 < d)
    (hdenom : d ≤ (1 - p.Bstar / q) ^ (t + 1))
    (h : Prefix (Snapshot I V) t) (out : Snapshot I V) :
    |occupancyResponse p q G A line l T t h out| ≤ (1 + p.Bstar) / d := by
  have hB : 0 < p.Bstar := by unfold Parameters.Bstar Parameters.smin; positivity
  have hnonneg : 0 ≤ (1 + p.Bstar) / d := by positivity
  unfold occupancyResponse
  split
  · split
    · exact performed_rescaled_occupancy_jump p q t hc hq hfactor A line l _
        (fun x hx => hT x (occupancyPrefix_subset q A line l T t h hx)) d hd hdenom _
    · simpa using hnonneg
  · simpa using hnonneg

theorem occupancyResponse_mean_nonnegative (p : Parameters) (q t : ℕ) (G : Input I V)
    (hc : 0 < p.c) (hq : 0 < q) (hscale : p.smin ≤ p.sizeScale q t)
    (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) (h : Prefix (Snapshot I V) t) :
    0 ≤ ∑ out, (snapshotPMF p q t G (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩) out).toReal *
      occupancyResponse p q G A line l T t h out := by
  simp_rw [snapshotPMF_apply_real]
  rw [sum_snapshotWeight_response]
  cases hb : (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1 with
  | none => simp [drawStepWeight, occupancyResponse, hb]
  | some S =>
    by_cases hp : Precheck p q t G S
    · rw [sum_drawStepWeight_of_precheck p q t G S hp]
      simp only [occupancyResponse, hb, hp, ite_true]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
        sum_noiseWeight p q G S hp.1 (fun i hi => (hp.2.2.2.1 i hi).1), one_mul]
      exact sub_nonneg.mpr (performed_rescaled_occupancy_ge p q t G S hp hc hq
        hscale hfactor A index line hline l _
          (fun x hx => hT x (occupancyPrefix_subset q A line l T t h hx)))
    · simp [drawStepWeight, occupancyResponse, hb, hp]

theorem occupancyTrack_lower_tail (p : Parameters) (q N : ℕ) (G : Input I V)
    (hc : 0 < p.c) (hq : 0 < q) (hN : 1 ≤ N)
    (hscale : ∀ t < N, p.smin ≤ p.sizeScale q t)
    (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) (d : ℝ) (hd : 0 < d)
    (hdenom : ∀ t < N, d ≤ (1 - p.Bstar / q) ^ (t + 1))
    (u : ℝ) (hu : 0 < u) (t : ℕ) (ht : t ≤ N) :
    (snapshotPathLaw p q G).real
      {ω | occupancyTrack p q G A line l T t ω ≤ (T.card : ℝ) - u} ≤
      2 * Real.exp (-u ^ 2 / (8 * (N : ℝ) * ((1 + p.Bstar) / d) ^ 2)) := by
  have hB : 0 < p.Bstar := by unfold Parameters.Bstar Parameters.smin; positivity
  exact additiveTrack_lower_tail (fun n => snapshotPMF p q n G) initialSnapshot
    (T.card : ℝ) (occupancyResponse p q G A line l T) N ((1 + p.Bstar) / d)
    hN (by positivity)
    (fun j hj h out => occupancyResponse_bound p q j G hc hq hfactor A line l T
      hT d hd (hdenom j hj) h out)
    (fun j hj h => occupancyResponse_mean_nonnegative p q j G hc hq (hscale j hj)
      hfactor A index line hline l T hT h) u hu t ht

end Balanced.Selection.Process

end

end OAI
