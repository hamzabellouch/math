import OAI.Computability.UniqueGames.Foundations.FiniteTrialsLemmas
import OAI.Computability.UniqueGames.Foundations.Rectangle

namespace OAI

section

/-! Per-label diagonal lower bounds for the actual finite shared sampler.
These bounds retain the output label, which is necessary for comparing the
sampler's output distribution with a prescribed diagonal distribution. -/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

def localSample (accept : σ → Bool) (decode : σ → α) (fallback : α)
    (proposals : List σ) : α :=
  ((firstAccepted accept proposals).map decode).getD fallback

def localDiagonal (left right : σ → Bool) (decode : σ → α) (fallback a : α)
    (proposals : List σ) : ℝ :=
  if localSample left decode fallback proposals = a ∧
      localSample right decode fallback proposals = a then 1 else 0

def goodLabel (left right : σ → Bool) (decode : σ → α) (a : α) (s : σ) : Bool :=
  (left s && right s) && decide (decode s = a)

omit [Fintype σ] [DecidableEq σ] in
theorem common_first_label_lower (left right : σ → Bool) (decode : σ → α)
    (fallback a : α) (proposals : List σ) :
    goodFirstIndicator (fun s => left s || right s) (goodLabel left right decode a) proposals ≤
      localDiagonal left right decode fallback a proposals := by
  cases hfirst : firstAccepted (fun s => left s || right s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      unfold localDiagonal
      split_ifs <;> norm_num
  | some s =>
      by_cases hc : goodLabel left right decode a s = true
      · have hparts : (left s = true ∧ right s = true) ∧ decode s = a := by
          simpa [goodLabel] using hc
        have h := first_union_common left right proposals s hfirst hparts.1.1 hparts.1.2
        simp [goodFirstIndicator, hfirst, hc, localDiagonal, localSample, h.1, h.2, hparts.2]
      · have hn : 0 ≤ localDiagonal left right decode fallback a proposals := by
          unfold localDiagonal
          split_ifs <;> norm_num
        simpa [goodFirstIndicator, hfirst, hc] using hn

omit [DecidableEq σ] in theorem union_goodLabel_mass
    (w : σ → ℝ) (left right : σ → Bool) (decode : σ → α) (a : α) :
    eventMass w (fun s => (left s || right s) && goodLabel left right decode a s) =
      eventMass w (goodLabel left right decode a) := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro s _
  cases hl : left s <;> cases hr : right s <;> simp [goodLabel, hl, hr]

/-- The finite shared-list sampler's mass on the particular diagonal output
(a,a) is at least the common-first-label mass. Exhaustion uses a fixed local
fallback; its contribution is nonnegative and is not counted in this bound. -/
theorem finite_label_diagonal_bound (w : σ → ℝ) (left right : σ → Bool)
    (decode : σ → α) (fallback a : α) (hw : ∀ s, 0 ≤ w s)
    (hw_sum : ∑ s, w s = 1) (hu : 0 < eventMass w (fun s => left s || right s)) (n : Nat) :
    eventMass w (goodLabel left right decode a) / eventMass w (fun s => left s || right s) *
        (1 - eventMass w (fun s => !(left s || right s)) ^ n) ≤
      traceAverage w n (localDiagonal left right decode fallback a) := by
  have h := traceAverage_mono w hw n _ _ (common_first_label_lower left right decode fallback a)
  rw [goodFirstIndicator_law w _ _ hw_sum n,
    goodFirstMass_exact w _ _ hw_sum (ne_of_gt hu) n,
    union_goodLabel_mass] at h
  exact h

section Rectangle

variable [Fintype α] [Nonempty α]

/-- Concrete normalized-density instance of the per-label bound. All random
proposals come from the finite rectangle constructed from `thresholds`. -/
theorem rectangle_label_diagonal_bound (thresholds : List ℝ) (p q : α → ℝ)
    (fallback a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (hq1 : ∀ x, q x ≤ 1)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) (n : Nat) :
    min (p a) (q a) / (1 + totalVariation p q) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds p s || rectangleAccept thresholds q s)) ^ n) ≤
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds p) (rectangleAccept thresholds q)
          Prod.fst fallback a) := by
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hU : 0 < unionMass p q := by
    rw [unionMass_eq p q hpsum hqsum]
    linarith [totalVariation_nonneg p q]
  have hmass := rectangle_union_mass thresholds p q hpm hqm hp0 hq0 hp1 hq1
  have hu : 0 < eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds p s || rectangleAccept thresholds q s) := by
    rw [hmass]
    exact div_pos hU hc
  have h := finite_label_diagonal_bound (rectangleWeight thresholds)
    (rectangleAccept thresholds p) (rectangleAccept thresholds q) Prod.fst fallback a
    (rectangleWeight_nonnegative thresholds) (rectangleWeight_normalized thresholds) hu n
  unfold goodLabel at h
  rw [rectangle_common_label_mass thresholds p q a hpm hqm hp0 hq0 hp1 hq1, hmass] at h
  have hratio : (min (p a) (q a) / (Fintype.card α : ℝ)) /
      (unionMass p q / (Fintype.card α : ℝ)) = min (p a) (q a) / unionMass p q := by
    field_simp
  rw [hratio, unionMass_eq p q hpsum hqsum] at h
  exact h

end Rectangle

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
