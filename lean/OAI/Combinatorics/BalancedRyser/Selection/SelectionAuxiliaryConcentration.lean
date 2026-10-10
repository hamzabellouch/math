import OAI.Combinatorics.BalancedRyser.Probability.DriftUnionBound
import OAI.Combinatorics.BalancedRyser.Selection.SelectionAuxiliaryConditional

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

def domainTrackJumpBound (p : Parameters) (q : ℕ) : ℝ :=
  (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / p.smin

def degreeTrackJumpBound (p : Parameters) (q : ℕ) : ℝ :=
  (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
    (p.smin * p.a / 3)

theorem domainTrackJumpBound_pos {p : Parameters} (hp : p.Admissible) (q : ℕ) :
    0 < domainTrackJumpBound p q := by
  have hP := Parameters.Pstar_pos hp
  have hs : 0 < p.smin := Real.exp_pos _
  have hq : 0 ≤ (q : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  unfold domainTrackJumpBound
  positivity

theorem degreeTrackJumpBound_pos {p : Parameters} (hp : p.Admissible) (q : ℕ) :
    0 < degreeTrackJumpBound p q := by
  have hP := Parameters.Pstar_pos hp
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hC := hp.2.1
  have hq : 0 ≤ (q : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  unfold degreeTrackJumpBound
  positivity

theorem simultaneous_domainTrack_tail_of_mass {p : Parameters} (hp : p.Admissible)
    {q T : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hTpos : 1 ≤ T)
    (hT : T ≤ p.lastMainTime q (Fintype.card I))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ i j, j < T → ∀ S : State I V, Precheck p q j G S →
      i ∈ S.remaining → domainOverflowMass p q G S i ≤ ε)
    (u : ℝ) (hu : 0 < u) :
    (snapshotPathLaw p q G).real {ω | ∃ i t, t ≤ T ∧
      (t : ℝ) * ((q : ℝ) * ε / p.smin) + u ≤
        |domainTrack p q G i t ω - domainTrack p q G i 0 ω|} ≤
      2 * Fintype.card I * (T + 1 : ℕ) *
        Real.exp (-u ^ 2 / (8 * (T : ℝ) * (domainTrackJumpBound p q) ^ 2)) := by
  apply simultaneous_abs_tail_of_drift_bound
    (μ := snapshotPathLaw p q G) (ℱ := snapshotFiltration)
    (domainTrack p q G) T (domainTrackJumpBound p q) hTpos
    (domainTrackJumpBound_pos hp q)
  · intro i t _
    exact stronglyMeasurable_domainTrack p q G i t
  · intro i j hj
    exact Filter.Eventually.of_forall (fun ω =>
      abs_domainTrack_succ_sub_le hp hG hq hPq (by omega) i ω)
  · exact hu
  · intro i t ht
    exact ae_domainTrack_accumulated_drift_of_mass hp hG hq hPq hT ht i hε
      (fun j hj => hmass i j hj)

theorem simultaneous_degreeTrack_tail_of_mass {p : Parameters} (hp : p.Admissible)
    {q T : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hTpos : 1 ≤ T)
    (hT : T ≤ p.lastMainTime q (Fintype.card I))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ v j, j < T → ∀ S : State I V, Precheck p q j G S →
      S.remaining.card = Fintype.card I - j →
      v ∈ currentVertices G S → degreeCensorMass p q G S v ≤ ε)
    (u : ℝ) (hu : 0 < u) :
    (snapshotPathLaw p q G).real {ω | ∃ v t, t ≤ T ∧
      (t : ℝ) * (p.C * q * ε / (p.smin * p.a / 3)) + u ≤
        degreeTrack p q G v t ω - degreeTrack p q G v 0 ω} ≤
      2 * Fintype.card V * (T + 1 : ℕ) *
        Real.exp (-u ^ 2 / (8 * (T : ℝ) * (degreeTrackJumpBound p q) ^ 2)) := by
  apply simultaneous_upper_tail_of_drift_bound
    (μ := snapshotPathLaw p q G) (ℱ := snapshotFiltration)
    (degreeTrack p q G) T (degreeTrackJumpBound p q) hTpos
    (degreeTrackJumpBound_pos hp q)
  · intro v t _
    exact stronglyMeasurable_degreeTrack p q G v t
  · intro v j hj
    exact Filter.Eventually.of_forall (fun ω =>
      abs_degreeTrack_succ_sub_le hp hG hq hPq (by omega) v ω)
  · exact hu
  · intro v t ht
    exact ae_degreeTrack_accumulated_drift_of_mass hp hG hq hPq hT ht v hε
      (fun j hj => hmass v j hj)

end Balanced.Selection.Process

end

end OAI
