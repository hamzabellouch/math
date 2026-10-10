import OAI.Combinatorics.Ryser.LineCover.Rigidity

namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

universe u

def linecoverFailureBound (D : ℕ) (δ A q : ℝ) : ℝ :=
  2 * (1 + q * (q + 1)) *
      Real.exp (-q ^ (2 * (Incidence.savingExponent / 10)) / (16 * (D : ℝ) ^ 5)) +
    2 * (q * (q + 1)) ^ (2 * logarithmicSampleSize A q) *
      Real.exp (-tupleTailConstant D (10 * (D + 1)) δ *
        (logarithmicSampleSize A q : ℝ) ^ 2)

theorem prob_not_goodLineCover_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {D : ℕ} {δ ρ A : ℝ} (process : DeletionProcess F D δ)
    (hD : 0 < D) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (params : RigidityParameters D δ ρ A Incidence.savingExponent (Fintype.card F)) :
    process.law.prob (fun ω => ¬ GoodLineCover δ ρ ω) ≤
      linecoverFailureBound D δ A (Fintype.card F) := by
  let h := 10 * (D + 1)
  let t := logarithmicSampleSize A (Fintype.card F)
  have hh : 0 < h := by dsimp [h]; omega
  have ht : 0 < t := lt_of_lt_of_le hh params.h_t
  have hε : 0 < Incidence.savingExponent / 10 := by
    exact div_pos Incidence.savingExponent_pos (by norm_num)
  have hεhalf : Incidence.savingExponent / 10 ≤ 1 / 2 := by
    linarith [Incidence.savingExponent_lt_tenth]
  have hcounts := process.prob_not_goodCounts (Incidence.savingExponent / 10)
    (by omega : 1 ≤ D) hε hεhalf
  have htuples := process.prob_not_goodTuples h t hD hh ht hδ
  have hbad : process.law.prob (fun ω => ¬ GoodLineCover δ ρ ω) ≤
      process.law.prob (fun ω =>
        ¬ GoodCounts process (Incidence.savingExponent / 10) ω ∨
        ¬ GoodTuples process h t ω) := by
    apply process.law.prob_mono
    intro ω hnot
    by_cases hc : GoodCounts process (Incidence.savingExponent / 10) ω
    · right
      intro htup
      exact hnot (goodLineCover_of_goodCounts_goodTuples process hδ hρ hq hsub
        params ω hc htup)
    · exact Or.inl hc
  exact hbad.trans ((process.law.prob_union_le _ _).trans (add_le_add hcounts htuples))

theorem tendsto_linecoverFailureBound (D : ℕ) {δ A : ℝ}
    (hD : 0 < D) (hδ : 0 < δ)
    (hA : 5 / tupleTailConstant D (10 * (D + 1)) δ < A) :
    Tendsto (linecoverFailureBound D δ A) atTop (𝓝 0) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hc0 := tupleTailConstant_pos hD
    (show 0 < 10 * (D + 1) by omega) hδ
  have hc := tendsto_count_failure_atTop hDr
    (show 0 < Incidence.savingExponent / 10 from
      div_pos Incidence.savingExponent_pos (by norm_num))
  have ht := tendsto_tuple_failure_atTop hc0 hA
  unfold linecoverFailureBound
  simpa only [add_zero] using hc.add ht

theorem uniform_linecover_probability (D : ℕ) (δ ρ : ℝ)
    (hD : 0 < D) (hδ : 0 < δ) (hρ : 0 < ρ) (η : ℝ) (hη : 0 < η) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      Q ≤ Fintype.card F → Incidence.SmallProperSubfields F →
      ∀ process : DeletionProcess F D δ,
        1 - η ≤ process.law.prob (GoodLineCover δ ρ) := by
  let c0 := tupleTailConstant D (10 * (D + 1)) δ
  have hc0 : 0 < c0 := tupleTailConstant_pos hD (by omega) hδ
  let A := 6 / c0
  have hA : 0 < A := div_pos (by norm_num) hc0
  have hA5 : 5 / c0 < A := div_lt_div_of_pos_right (by norm_num) hc0
  have hnumeric := eventually_rigidityParameters D hδ hρ hA
    Incidence.savingExponent_pos Incidence.savingExponent_lt_tenth.le
  have hfailure : ∀ᶠ q : ℝ in atTop, linecoverFailureBound D δ A q ≤ η :=
    (tendsto_linecoverFailureBound D hD hδ hA5).eventually_le_const hη
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (hnumeric.and hfailure)
  refine ⟨max ⌈R⌉₊ Incidence.incidenceThreshold, ?_⟩
  intro F instField instFintype instDecidable hQ hsub process
  have hRcard : R ≤ (Fintype.card F : ℝ) :=
    (Nat.le_ceil R).trans (by
      exact_mod_cast (le_max_left ⌈R⌉₊ Incidence.incidenceThreshold).trans hQ)
  have hq : Incidence.incidenceThreshold ≤ Fintype.card F :=
    (le_max_right ⌈R⌉₊ Incidence.incidenceThreshold).trans hQ
  obtain ⟨params, hbound⟩ := hR (Fintype.card F) hRcard
  have hprob := (prob_not_goodLineCover_le process hD hδ hρ hq hsub params).trans hbound
  rw [process.law.prob_compl] at hprob
  linarith

end RyserCoveringCounterexample.LineCover

end

end OAI
