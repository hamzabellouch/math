import OAI.Combinatorics.BalancedRyser.Selection.SelectionAuxiliaryDrift
import OAI.Combinatorics.BalancedRyser.Selection.SelectionCensoredJumps

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in

theorem censoredDomainNumerator_eq_count (q : ℕ) (G : Input I V)
    (S : State I V) (r : Noise I V) (i : I) :
    censoredDomainNumerator q G S r i =
      (CensoredJumps.censoredDomainCount q G S i r.2.1 r.2.2 : ℝ) := by
  by_cases h : (((thinned G S r.2.1 r.2.2) ∩ domain G S i).card : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ)
  · simp only [censoredDomainNumerator, CensoredJumps.censoredDomainCount,
      ite_eq_right (not_lt.mpr h), ite_eq_left h]
  · simp only [censoredDomainNumerator, CensoredJumps.censoredDomainCount,
      ite_eq_left (lt_of_not_ge h), ite_eq_right h]

omit [Fintype I] in

theorem censoredDegreeNumerator_eq_count (q : ℕ) (G : Input I V)
    (S : State I V) (r : Noise I V) (v : V) :
    censoredDegreeNumerator q G S r v =
      (CensoredJumps.censoredDegreeCount q G S r.1 r.2.1 v r.2.2 : ℝ) := by
  by_cases he : r.2.1 ∈ G.exceptional v
  · simp [censoredDegreeNumerator, CensoredJumps.censoredDegreeCount, he]
  · by_cases h : (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ) ≤
        (q : ℝ) ^ (1 / 8 : ℝ)
    · simp only [censoredDegreeNumerator, CensoredJumps.censoredDegreeCount, he, false_or,
        not_false_eq_true, true_and, ite_eq_right (not_lt.mpr h), ite_eq_left h]
    · simp only [censoredDegreeNumerator, CensoredJumps.censoredDegreeCount, he, false_or,
        not_false_eq_true, true_and, ite_eq_left (lt_of_not_ge h), ite_eq_right h]

theorem abs_domainTrackIncrement_le {p : Parameters} (hp : p.Admissible)
    {G : Input I V} {q t : ℕ} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I)) (i : I)
    (before : Option (State I V)) (draw : Option (Noise I V)) :
    |domainTrackIncrement p q t G i before draw| ≤
      (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / p.smin := by
  have hnon : 0 ≤ (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / p.smin := by
    have hP := (Parameters.Pstar_pos hp).le
    have hs := (Real.exp_pos (-6 * p.Pstar)).le
    change 0 ≤ (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / Real.exp (-6 * p.Pstar)
    positivity
  cases before with
  | none => simpa [domainTrackIncrement] using hnon
  | some S =>
    cases draw with
    | none => simpa [domainTrackIncrement] using hnon
    | some r =>
      by_cases hi : i ∈ S.remaining
      · simpa only [domainTrackIncrement, hi, ite_true, censoredDomainNumerator_eq_count] using
          CensoredJumps.abs_rescaled_censoredDomainCount_sub_le hp hG hq hPq ht S hi r.2.1 r.2.2
      · simpa [domainTrackIncrement, hi] using hnon

theorem abs_degreeTrackIncrement_le {p : Parameters} (hp : p.Admissible)
    {G : Input I V} {q t : ℕ} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I)) (v : V)
    (before : Option (State I V)) (draw : Option (Noise I V)) :
    |degreeTrackIncrement p q t G v before draw| ≤
      (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
        (p.smin * p.a / 3) := by
  have hnon : 0 ≤
      (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
        (p.smin * p.a / 3) := by
    have hP := (Parameters.Pstar_pos hp).le
    have hC := hp.2.1.le
    have ha := (Parameters.a_bounds hp).1.le
    change 0 ≤ (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
      (Real.exp (-6 * p.Pstar) * p.a / 3)
    positivity
  cases before with
  | none => simpa [degreeTrackIncrement] using hnon
  | some S =>
    cases draw with
    | none => simpa [degreeTrackIncrement] using hnon
    | some r =>
      by_cases hv : v ∈ currentVertices G S
      · simpa only [degreeTrackIncrement, hv, ite_true, censoredDegreeNumerator_eq_count] using
          CensoredJumps.abs_rescaled_censoredDegreeCount_sub_le hp hG hq hPq ht S r.1 r.2.1 v r.2.2
      · simpa [degreeTrackIncrement, hv] using hnon

theorem abs_domainTrack_succ_sub_le {p : Parameters} (hp : p.Admissible)
    {G : Input I V} {q t : ℕ} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (i : I) (ω : FiniteHistory.Path (Snapshot I V)) :
    |domainTrack p q G i (t + 1) ω - domainTrack p q G i t ω| ≤
      (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / p.smin := by
  rw [domainTrack_succ_sub]
  exact abs_domainTrackIncrement_le hp hG hq hPq ht i _ _

theorem abs_degreeTrack_succ_sub_le {p : Parameters} (hp : p.Admissible)
    {G : Input I V} {q t : ℕ} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (v : V) (ω : FiniteHistory.Path (Snapshot I V)) :
    |degreeTrack p q G v (t + 1) ω - degreeTrack p q G v t ω| ≤
      (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
        (p.smin * p.a / 3) := by
  rw [degreeTrack_succ_sub]
  exact abs_degreeTrackIncrement_le hp hG hq hPq ht v _ _

end Balanced.Selection.Process

end

end OAI
