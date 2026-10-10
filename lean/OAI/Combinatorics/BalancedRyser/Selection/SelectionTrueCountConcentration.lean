import OAI.Combinatorics.BalancedRyser.Selection.SelectionAuxiliaryConcentration

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem abs_count_error_le_of_rescaled {x x₀ s A : ℝ}
    (hs : 0 < s) (hsone : s ≤ 1) (h : |x / s - x₀| ≤ A) :
    |x - s * x₀| ≤ A := by
  have he : x - s * x₀ = s * (x / s - x₀) := by field_simp
  rw [he, abs_mul, abs_of_pos hs]
  exact (mul_le_of_le_one_left (abs_nonneg _) hsone).trans h

theorem count_upper_error_le_of_rescaled {x x₀ s A : ℝ}
    (hs : 0 < s) (hsone : s ≤ 1) (hA : 0 ≤ A) (h : x / s - x₀ ≤ A) :
    x ≤ s * x₀ + A := by
  have he : x - s * x₀ = s * (x / s - x₀) := by field_simp
  have hu : x - s * x₀ ≤ A := by
    rw [he]
    exact (mul_le_mul_of_nonneg_left h hs.le).trans
      (mul_le_of_le_one_left hA hsone)
  linarith

theorem ae_true_counts_of_track_bounds {p : Parameters} (hp : p.Admissible)
    {q T : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (hT : T ≤ p.lastMainTime q (Fintype.card I))
    (A : ℝ) (hA : 0 ≤ A) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      (∀ i t, t ≤ T → |domainTrack p q G i t ω - domainTrack p q G i 0 ω| ≤ A) →
      (∀ v t, t ≤ T → degreeTrack p q G v t ω - degreeTrack p q G v 0 ω ≤ A) →
      ∀ t S, t ≤ T → (ω t).1 = some S →
        (∀ i ∈ S.remaining,
          |((domain G S i).card : ℝ) - p.sizeScale q t * (domain G initialState i).card| ≤ A) ∧
        (∀ v ∈ currentVertices G S,
          (degree G S v : ℝ) ≤
            p.degreeScale q (Fintype.card I) t * degree G initialState v + A) := by
  filter_upwards [ae_domainTrack_agreement p q G, ae_degreeTrack_agreement p q G hG]
    with ω hdom hdeg
  intro hdomBound hdegBound t S ht hS
  have hscale := Parameters.source_scale_bounds hp hq hPq hG.1 (ht.trans hT)
  have hs : 0 < p.sizeScale q t := (Real.exp_pos _).trans_le hscale.1
  have hb : 0 < p.degreeScale q (Fintype.card I) t := by
    have hsmin : 0 < p.smin := Real.exp_pos _
    have ha := (Parameters.a_bounds hp).1
    have hmin : 0 < p.smin * p.a / 3 := by positivity
    exact hmin.trans_le hscale.2.2.1
  constructor
  · intro i hi
    apply abs_count_error_le_of_rescaled hs hscale.2.1
    simpa only [hdom i t S hS hi, domainTrack_zero] using hdomBound i t ht
  · intro v hv
    apply count_upper_error_le_of_rescaled hb hscale.2.2.2 hA
    simpa only [hdeg v t S hS hv, degreeTrack_zero] using hdegBound v t ht

theorem true_count_failure_probability_le {p : Parameters} (hp : p.Admissible)
    {q T : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hTpos : 1 ≤ T)
    (hT : T ≤ p.lastMainTime q (Fintype.card I))
    {εd εv : ℝ} (hεd : 0 ≤ εd) (hεv : 0 ≤ εv)
    (hmassd : ∀ i j, j < T → ∀ S : State I V, Precheck p q j G S →
      i ∈ S.remaining → domainOverflowMass p q G S i ≤ εd)
    (hmassv : ∀ v j, j < T → ∀ S : State I V, Precheck p q j G S →
      S.remaining.card = Fintype.card I - j →
      v ∈ currentVertices G S → degreeCensorMass p q G S v ≤ εv)
    (u A : ℝ) (hu : 0 < u) (hA : 0 ≤ A)
    (hDd : ∀ t ≤ T, (t : ℝ) * ((q : ℝ) * εd / p.smin) + u ≤ A)
    (hDv : ∀ t ≤ T, (t : ℝ) * (p.C * q * εv / (p.smin * p.a / 3)) + u ≤ A) :
    (snapshotPathLaw p q G).real {ω | ¬ (∀ t S, t ≤ T → (ω t).1 = some S →
      (∀ i ∈ S.remaining,
        |((domain G S i).card : ℝ) - p.sizeScale q t * (domain G initialState i).card| ≤ A) ∧
      (∀ v ∈ currentVertices G S, (degree G S v : ℝ) ≤
        p.degreeScale q (Fintype.card I) t * degree G initialState v + A))} ≤
      2 * Fintype.card I * (T + 1 : ℕ) *
        Real.exp (-u ^ 2 / (8 * (T : ℝ) * (domainTrackJumpBound p q) ^ 2)) +
      2 * Fintype.card V * (T + 1 : ℕ) *
        Real.exp (-u ^ 2 / (8 * (T : ℝ) * (degreeTrackJumpBound p q) ^ 2)) := by
  let E := {ω | ∃ i t, t ≤ T ∧ (t : ℝ) * ((q : ℝ) * εd / p.smin) + u ≤
    |domainTrack p q G i t ω - domainTrack p q G i 0 ω|}
  let F := {ω | ∃ v t, t ≤ T ∧ (t : ℝ) *
    (p.C * q * εv / (p.smin * p.a / 3)) + u ≤
      degreeTrack p q G v t ω - degreeTrack p q G v 0 ω}
  have hsub : (snapshotPathLaw p q G).real {ω | ¬ (∀ t S, t ≤ T → (ω t).1 = some S →
      (∀ i ∈ S.remaining,
        |((domain G S i).card : ℝ) - p.sizeScale q t * (domain G initialState i).card| ≤ A) ∧
      (∀ v ∈ currentVertices G S, (degree G S v : ℝ) ≤
        p.degreeScale q (Fintype.card I) t * degree G initialState v + A))} ≤
      (snapshotPathLaw p q G).real (E ∪ F) := by
    apply measureReal_le_of_ae_imp
    filter_upwards [ae_true_counts_of_track_bounds hp hG hq hPq hT A hA] with ω hω
    intro hbad
    by_contra hgood
    have hne : ω ∉ E := fun h => hgood (Or.inl h)
    have hnf : ω ∉ F := fun h => hgood (Or.inr h)
    apply hbad (hω ?_ ?_)
    · intro i t ht
      by_contra h
      exact hne ⟨i, t, ht, (hDd t ht).trans (le_of_lt (lt_of_not_ge h))⟩
    · intro v t ht
      by_contra h
      exact hnf ⟨v, t, ht, (hDv t ht).trans (le_of_lt (lt_of_not_ge h))⟩
  exact hsub.trans ((measureReal_union_le E F).trans
    (add_le_add (simultaneous_domainTrack_tail_of_mass hp hG hq hPq hTpos hT
      hεd hmassd u hu) (simultaneous_degreeTrack_tail_of_mass hp hG hq hPq hTpos hT
      hεv hmassv u hu)))

end Balanced.Selection.Process

end

end OAI
