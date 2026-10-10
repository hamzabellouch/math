import OAI.Algebra.DepthFive.LocalMomentPairing
import OAI.Algebra.DepthFive.LocalProductAverage

namespace OAI

/-! Actual finite occupation averages feed the normalized pairing sum. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing
open Pairings

def layerMeanV (γ : Type*) [Fintype γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) (a : ℕ) : ℝ :=
  (a : ℝ) / Fintype.card {v : Fin (L + 1) × (γ × γ) // side v.1 = true}

def layerMeanU (γ : Type*) [Fintype γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) (b : ℕ) : ℝ :=
  (b : ℝ) / Fintype.card {v : Fin (L + 1) × (γ × γ) // ¬ side v.1 = true}

def occupationPathMean {γ : Type*} [Fintype γ] [DecidableEq γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) (a b : ℕ)
    (endpoint : γ) (x : Fin L → Labels γ) : ℝ :=
  partitionCompositionMean (fun v : Fin (L + 1) × (γ × γ) => side v.1)
    (fun M => ∏ t, LocalMoments.localPolynomial (side t) (fun y => M (t, y))
      (layerLabels endpoint x t).p (layerLabels endpoint x t).q
      (layerLabels endpoint x t).r) a b

/-- The true two-group uniform average is bounded by the geometric local
table. Both variable groups are nonempty; no moment hypothesis is assumed. -/
theorem occupationPathMean_le_geometric {γ : Type*} [Fintype γ] [DecidableEq γ]
    {L : ℕ} (side : Fin (L + 1) → Bool)
    [Nonempty {v : Fin (L + 1) × (γ × γ) // side v.1 = true}]
    [Nonempty {v : Fin (L + 1) × (γ × γ) // ¬ side v.1 = true}]
    (a b : ℕ) (endpoint : γ) (x : Fin L → Labels γ) :
    occupationPathMean side a b endpoint x ≤
      pathGeometricMoment side (layerMeanV γ side a) (layerMeanU γ side b)
        endpoint (classifyWord endpoint x) x := by
  have h := LocalMoments.partitionCompositionMean_layered_restrict_le side a b
    Finset.univ (fun t => (layerLabels endpoint x t).p)
      (fun t => (layerLabels endpoint x t).q) (fun t => (layerLabels endpoint x t).r)
  rw [← prod_localGeometricMass_eq]
  simpa [occupationPathMean, layerMeanV, layerMeanU] using h

/-- Actual occupation averaging, normalizing, and relaxing the four-path
classes combine without a residual analytic comparison hypothesis. -/
theorem sum_occupationPathMean_le {γ : Type*} [Fintype γ] [DecidableEq γ]
    {L : ℕ} (side : Fin (L + 1) → Bool)
    [Nonempty {v : Fin (L + 1) × (γ × γ) // side v.1 = true}]
    [Nonempty {v : Fin (L + 1) × (γ × γ) // ¬ side v.1 = true}]
    (a b : ℕ) (ha : 0 < a) (endpoint : γ) :
    (∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
      occupationPathMean side a b endpoint x.1) ≤
    pathMean side (layerMeanV γ side a) (layerMeanU γ side b) ^ 2 *
      ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
        pathWeight side
          (layerMeanV γ side a / (layerMeanV γ side a + 1))
          (layerMeanU γ side b / (layerMeanU γ side b + 1)) endpoint τ x.1 := by
  have hA : 0 < layerMeanV γ side a := by
    unfold layerMeanV
    exact div_pos (by exact_mod_cast ha) (by exact_mod_cast Fintype.card_pos)
  have hB : 0 ≤ layerMeanU γ side b := by unfold layerMeanU; positivity
  calc
    _ ≤ ∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
        pathGeometricMoment side (layerMeanV γ side a) (layerMeanU γ side b)
          endpoint (classifyWord endpoint x.1) x.1 := by
      apply Finset.sum_le_sum
      intro x _
      exact occupationPathMean_le_geometric side a b endpoint x.1
    _ ≤ _ := sum_compatible_geometricMoment_le side hA hB endpoint

end Problem335.MomentPairing

end

end OAI
