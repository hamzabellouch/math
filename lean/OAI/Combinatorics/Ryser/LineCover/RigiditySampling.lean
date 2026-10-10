import OAI.Combinatorics.Ryser.LineCover.HeavyIncidence
import OAI.Combinatorics.Ryser.LineCover.MaxConcurrency
import OAI.Combinatorics.Ryser.LineCover.LowConcurrency
import OAI.Combinatorics.Ryser.LineCover.HighConcurrency
import OAI.Combinatorics.Ryser.LineCover.RigidityParameters

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exists_admissible_of_no_large_pencil
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D : ℕ) (δ ρ A : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ)
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (params : RigidityParameters D δ ρ A Incidence.savingExponent (Fintype.card F))
    (hsparse : SparseShapes shapes D)
    (hshapes : shapes.card ≤ D * Fintype.card F ^ D)
    (hL : L.card ≤ Fintype.card F)
    (hE : (overlapExcess Incidence X L : ℝ) ≤
      rigidityBudget D Incidence.savingExponent (Fintype.card F))
    (hgap : (Fintype.card F : ℝ) - L.card ≤
      rigidityBudget D Incidence.savingExponent (Fintype.card F) /
        (δ * Fintype.card F))
    (hsmall : ∀ p : ProjectivePoint F,
      ((coverPencil L p).card : ℝ) < (1 - ρ) * Fintype.card F) :
    ∃ a : LineTuple F (logarithmicSampleSize A (Fintype.card F)),
      (∀ i, a i ∈ L) ∧ AdmissibleTuple shapes D (10 * (D + 1)) a ∧
        ((X ∩ crossPoints a).card : ℝ) <
          δ * (logarithmicSampleSize A (Fintype.card F) : ℝ) ^ 2 / 2 := by
  let q : ℝ := Fintype.card F
  let κ : ℝ := Incidence.savingExponent
  let t := logarithmicSampleSize A q
  let h := 10 * (D + 1)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one params.q_one
  have hκ : 0 ≤ κ := Incidence.savingExponent_pos.le
  have hm : q / 2 ≤ (L.card : ℝ) := by
    have hg := params.gap_half
    linarith
  have hcount : q - rigidityBudget D κ q / (δ * q) ≤ (L.card : ℝ) := by
    linarith
  have hh : 1 ≤ h := by dsimp [h]; omega
  have ht : 0 < t := lt_of_lt_of_le Nat.zero_lt_one (hh.trans params.h_t)
  have hK : (shapes.card : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ) := by
    have hhcast : (shapes.card : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) ^ D := by
      exact_mod_cast hshapes
    simpa only [Real.rpow_natCast] using hhcast
  by_cases hlow : (maxConcurrency L : ℝ) ≤ q ^ (1 / 2 + κ / 4)
  · have hheavy : ((heavyPoints Incidence X L (q ^ (1 / 2 - κ / 3))).card : ℝ) ≤
        q ^ (1 + κ) :=
      (heavyPoints_card_le_of_excess X L _ _ params.T_one hE).trans params.heavy
    have hpair := orderedPairMass_le_of_uniform_incidence hq hsub X L
      (q ^ (1 / 2 - κ / 3)) (maxConcurrency L)
      (Real.rpow_nonneg hqpos.le _) (Nat.cast_nonneg _) hheavy hL
      (fun p => Nat.cast_le.mpr (coverPencil_card_le_maxConcurrency L p))
    have hratio := rigidity_pair_ratio_le D params.q_one hκ hm hlow hE hpair
    have hm4 : 4 ≤ L.card := by exact_mod_cast params.m_four.trans hm
    have hmH : 4 * h ≤ L.card := by exact_mod_cast params.m_h.trans hm
    have hmT : 2 * t ≤ L.card := by exact_mod_cast params.m_t.trans hm
    have hfailure : lowFailureBound X L shapes D (maxConcurrency L) h t δ < 1 := by
      have hbound := low_sampling_failure_le_envelope (A := A) D L.card (maxConcurrency L)
        shapes.card hqpos hδ hm hm4 hmH
        (Nat.cast_nonneg (orderedPairMass Incidence X L)) hlow hK hratio
      exact (show lowFailureBound X L shapes D (maxConcurrency L) h t δ ≤
        lowFailureEnvelope D δ A κ q from hbound).trans_lt params.low
    exact exists_low_sample_of_failureBound_lt_one X L shapes D (maxConcurrency L)
      h t δ hδ ht hmT (by omega) hsparse
      (coverPencil_card_le_maxConcurrency L) hfailure
  · let p := maxCenter L
    have hR : q ^ (1 / 2 + κ / 4) ≤ ((coverPencil L p).card : ℝ) :=
      (lt_of_not_ge hlow).le
    have hN : ρ * q / 2 ≤ ((L \ coverPencil L p).card : ℝ) :=
      complement_card_ge_half_of_no_large_pencil L q ρ
        (rigidityBudget D κ q) δ hcount params.gap_rho hsmall p
    have htR : t ≤ (coverPencil L p).card := by exact_mod_cast params.r_t.trans hR
    have htN : t ≤ (L \ coverPencil L p).card := by exact_mod_cast params.n_t.trans hN
    have hhR : 2 * h ≤ (coverPencil L p).card := by exact_mod_cast params.r_h.trans hR
    have hhN : 2 * h ≤ (L \ coverPencil L p).card := by exact_mod_cast params.n_h.trans hN
    have hfailure : highFailureBound X L p shapes D h t δ < 1 := by
      have hbound := high_sampling_failure_le_envelope (A := A) D (coverPencil L p).card
        (L \ coverPencil L p).card shapes.card hqpos hδ hρ
        (Nat.cast_nonneg (overlapExcess Incidence X L))
        (hE.trans (rigidityBudget_le D hκ params.q_one)) hR hN hhR hhN hK
      exact (show highFailureBound X L p shapes D h t δ ≤
        highFailureEnvelope D δ ρ A κ q from hbound).trans_lt params.high
    exact highConcurrency_exists_admissible X L p shapes D h t δ hsparse hδ
      hh params.h_t htR htN hfailure

end RyserCoveringCounterexample.LineCover

end

end OAI
