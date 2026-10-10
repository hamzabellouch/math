import OAI.Combinatorics.Ryser.LineCover.GoodCounts
import OAI.Combinatorics.Ryser.LineCover.GoodTuples
import OAI.Combinatorics.Ryser.LineCover.CoverEstimates
import OAI.Combinatorics.Ryser.LineCover.RigiditySampling

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ ρ A : ℝ}

theorem goodLineCover_of_goodCounts_goodTuples
    (process : DeletionProcess F D δ) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (params : RigidityParameters D δ ρ A Incidence.savingExponent (Fintype.card F))
    (ω : process.Config)
    (hcounts : GoodCounts process (Incidence.savingExponent / 10) ω)
    (htuples : GoodTuples process (10 * (D + 1))
      (logarithmicSampleSize A (Fintype.card F)) ω) :
    GoodLineCover δ ρ ω := by
  let q : ℝ := Fintype.card F
  let κ : ℝ := Incidence.savingExponent
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one params.q_one
  have hτ : δ * q ≤ process.survival * q :=
    mul_le_mul_of_nonneg_right process.survivalLower hqpos.le
  refine ⟨?_, ?_⟩
  · intro l
    have hl := (hcounts.2 l).1
    have herr := params.lineerror
    change δ * q / 2 ≤ retainedCount {linePoints l} (linePoints l) ω
    linarith
  · intro L hL hmiss
    by_contra hnone
    have hsmall (p : ProjectivePoint F) :
        ((coverPencil L p).card : ℝ) < (1 - ρ) * q :=
      lt_of_not_ge (fun hp => hnone ⟨p, hp⟩)
    let K := cleanLines ω L
    have hK : K.card ≤ Fintype.card F :=
      (Finset.card_le_card (cleanLines_subset ω L)).trans hL
    have hsmallK (p : ProjectivePoint F) :
        ((coverPencil K p).card : ℝ) < (1 - ρ) * q :=
      (Nat.cast_le.mpr (Finset.card_le_card
        (coverPencil_mono (cleanLines_subset ω L) p))).trans_lt (hsmall p)
    have htotal : process.survival * q ^ 2 - q ^ (3 / 2 + κ / 10) ≤
        ((survivors ∅ ω).card : ℝ) := by
      have h := (abs_le.mp hcounts.1).1
      linarith
    have hlines (l : AffineLine F) :
        ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ) ≤
          process.survival * q + ((D : ℝ) + q ^ (1 / 2 + κ / 10)) := by
      have h := (hcounts.2 l).2
      change retainedCount {linePoints l} (linePoints l) ω ≤ _
      linarith
    have hmissR : ((survivors ∅ ω \ L.biUnion linePoints).card : ℝ) ≤ 2 * q := by
      dsimp only [q]
      exact_mod_cast hmiss
    have hb := clean_cover_count_bounds ω L process.survival δ
      (q ^ (3 / 2 + κ / 10)) ((D : ℝ) + q ^ (1 / 2 + κ / 10)) (2 * q)
      hδ process.survivalLower (by positivity) htotal hlines hmissR hL
    have hbudget := rigidityBudget_eq_errors D (κ := κ) hqpos
    rw [← hbudget] at hb
    obtain ⟨a, haK, ha, hfew⟩ := exists_admissible_of_no_large_pencil
      (survivors ∅ ω) K process.shapes D δ ρ A hδ hρ hq hsub params
      process.sparse process.shapeCount hK hb.1 hb.2 hsmallK
    exact htuples.no_sparse_clean_tuple L a ha haK hfew

end RyserCoveringCounterexample.LineCover

end

end OAI
