import OAI.Combinatorics.BalancedRyser.Selection.SelectionAuxiliaryMeanBounds

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem ae_domainTrack_conditional_drift_of_mass {p : Parameters} (hp : p.Admissible)
    {q t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (i : I) {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ S : State I V, Precheck p q t G S → i ∈ S.remaining →
      domainOverflowMass p q G S i ≤ ε) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      |(snapshotPathLaw p q G)[fun ω =>
        domainTrack p q G i (t + 1) ω - domainTrack p q G i t ω |
          snapshotFiltration t] ω| ≤ (q : ℝ) * ε / p.smin := by
  have hbound : 0 ≤ (q : ℝ) * ε / p.smin := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg q) hε) (Real.exp_pos _).le
  filter_upwards [condExp_domainTrack_increment p q t G i] with ω hω
  rw [hω]
  cases hstate : (ω t).1 with
  | none => simpa [domainTrackIncrement] using hbound
  | some S =>
      by_cases hpre : Precheck p q t G S
      · rw [sum_drawStepWeight_of_precheck p q t G S hpre]
        by_cases hi : i ∈ S.remaining
        · exact (domainTrack_noise_drift_bound hp hG hq hPq ht S hpre i hi).trans
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hmass S hpre hi) (Nat.cast_nonneg q))
              (Real.exp_pos _).le)
        · simpa [domainTrackIncrement, hi] using hbound
      · simpa [Fintype.sum_option, drawStepWeight, hpre, domainTrackIncrement]
          using hbound

theorem ae_degreeTrack_conditional_drift_of_mass {p : Parameters} (hp : p.Admissible)
    {q t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (v : V) {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ S : State I V, Precheck p q t G S →
      S.remaining.card = Fintype.card I - t → v ∈ currentVertices G S →
      degreeCensorMass p q G S v ≤ ε) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      (snapshotPathLaw p q G)[fun ω =>
        degreeTrack p q G v (t + 1) ω - degreeTrack p q G v t ω |
          snapshotFiltration t] ω ≤ p.C * q * ε / (p.smin * p.a / 3) := by
  have hmin : 0 < p.smin * p.a / 3 := by
    have hs : 0 < p.smin := Real.exp_pos _
    have ha := (Parameters.a_bounds hp).1
    positivity
  have hcoeff : 0 ≤ p.C * q := mul_nonneg hp.2.1.le (Nat.cast_nonneg q)
  have hbound : 0 ≤ p.C * q * ε / (p.smin * p.a / 3) :=
    div_nonneg (mul_nonneg hcoeff hε) hmin.le
  filter_upwards [condExp_degreeTrack_increment p q t G v,
    ae_snapshot_remaining_card p q G] with ω hω hcard
  rw [hω]
  cases hstate : (ω t).1 with
  | none => simpa [degreeTrackIncrement] using hbound
  | some S =>
      by_cases hpre : Precheck p q t G S
      · rw [sum_drawStepWeight_of_precheck p q t G S hpre]
        by_cases hv : v ∈ currentVertices G S
        · exact (degreeTrack_noise_drift_bound hp hG hq hPq ht S hpre
            (hcard t S hstate) v hv).trans
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hmass S hpre (hcard t S hstate) hv) hcoeff) hmin.le)
        · simpa [degreeTrackIncrement, hv] using hbound
      · simpa [Fintype.sum_option, drawStepWeight, hpre, degreeTrackIncrement]
          using hbound

theorem ae_domainTrack_accumulated_drift_of_mass {p : Parameters} (hp : p.Admissible)
    {q T t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (hT : T ≤ p.lastMainTime q (Fintype.card I)) (ht : t ≤ T)
    (i : I) {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ j < T, ∀ S : State I V, Precheck p q j G S → i ∈ S.remaining →
      domainOverflowMass p q G S i ≤ ε) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      |∑ j ∈ Finset.range t, (snapshotPathLaw p q G)[fun ω =>
        domainTrack p q G i (j + 1) ω - domainTrack p q G i j ω |
          snapshotFiltration j] ω| ≤ (t : ℝ) * ((q : ℝ) * ε / p.smin) := by
  have hstep : ∀ j ∈ Finset.range t, ∀ᵐ ω ∂snapshotPathLaw p q G,
      |(snapshotPathLaw p q G)[fun ω =>
        domainTrack p q G i (j + 1) ω - domainTrack p q G i j ω |
          snapshotFiltration j] ω| ≤ (q : ℝ) * ε / p.smin := by
    intro j hj
    have hjt := Finset.mem_range.mp hj
    exact ae_domainTrack_conditional_drift_of_mass hp hG hq hPq (by omega)
      i hε (hmass j (by omega))
  filter_upwards [ae_all_iff.2 (fun j => ae_all_iff.2 (hstep j))] with ω hω
  calc
    _ ≤ ∑ j ∈ Finset.range t, |(snapshotPathLaw p q G)[fun ω =>
        domainTrack p q G i (j + 1) ω - domainTrack p q G i j ω |
          snapshotFiltration j] ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range t, (q : ℝ) * ε / p.smin :=
      Finset.sum_le_sum hω
    _ = _ := by simp

theorem ae_degreeTrack_accumulated_drift_of_mass {p : Parameters} (hp : p.Admissible)
    {q T t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (hT : T ≤ p.lastMainTime q (Fintype.card I)) (ht : t ≤ T)
    (v : V) {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ j < T, ∀ S : State I V, Precheck p q j G S →
      S.remaining.card = Fintype.card I - j →
      v ∈ currentVertices G S → degreeCensorMass p q G S v ≤ ε) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      (∑ j ∈ Finset.range t, (snapshotPathLaw p q G)[fun ω =>
        degreeTrack p q G v (j + 1) ω - degreeTrack p q G v j ω |
          snapshotFiltration j] ω) ≤
            (t : ℝ) * (p.C * q * ε / (p.smin * p.a / 3)) := by
  have hstep : ∀ j ∈ Finset.range t, ∀ᵐ ω ∂snapshotPathLaw p q G,
      (snapshotPathLaw p q G)[fun ω =>
        degreeTrack p q G v (j + 1) ω - degreeTrack p q G v j ω |
          snapshotFiltration j] ω ≤ p.C * q * ε / (p.smin * p.a / 3) := by
    intro j hj
    have hjt := Finset.mem_range.mp hj
    exact ae_degreeTrack_conditional_drift_of_mass hp hG hq hPq (by omega)
      v hε (hmass j (by omega))
  filter_upwards [ae_all_iff.2 (fun j => ae_all_iff.2 (hstep j))] with ω hω
  calc
    _ ≤ ∑ _j ∈ Finset.range t, p.C * q * ε / (p.smin * p.a / 3) :=
      Finset.sum_le_sum hω
    _ = _ := by simp

end Balanced.Selection.Process

end

end OAI
