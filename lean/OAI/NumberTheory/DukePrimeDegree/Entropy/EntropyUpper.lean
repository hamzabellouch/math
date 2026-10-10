import OAI.NumberTheory.PrimePackets.ShannonEntropy

namespace OAI

/-!
# Entropy bounds from a small collection of orbit names

This is the finite-partition estimate used in an entropy upper bound:
if all but a small mass lies on a short list of names, the entropy is
bounded by the logarithm of that list, plus the cost of the exceptional
mass. No dynamical covering or leafwise estimate is assumed here.
-/

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology Classical

namespace DukePrimeDegree

open PrimeDegreePackets

/-- A finite distribution concentrated on a list of names has small
entropy. The binary coding cost is at most `log 2`. -/
theorem finiteShannon_le_good_card {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (G : Finset α) (hG : G.Nonempty) :
    finiteShannon p ≤ Real.log 2 + Real.log G.card +
      (∑ a, if a ∈ G then 0 else p a) * Real.log (Fintype.card α) := by
  have hm : 0 < (G.card : ℝ) := by exact_mod_cast hG.card_pos
  have hn : 0 < (Fintype.card α : ℝ) :=
    lt_of_lt_of_le hm (by exact_mod_cast G.card_le_univ)
  let q : α → ℝ := fun a =>
    ((Fintype.card α : ℝ)⁻¹ + if a ∈ G then (G.card : ℝ)⁻¹ else 0) / 2
  have hqpos a : 0 < q a := by
    dsimp [q]
    split_ifs <;> positivity
  have hq1 : ∑ a, q a = 1 := by
    have hg : (∑ a : α, if a ∈ G then (G.card : ℝ)⁻¹ else 0) = 1 := by
      rw [Finset.sum_ite_mem]
      simp [ne_of_gt hm]
    change (∑ a : α, ((Fintype.card α : ℝ)⁻¹ +
      if a ∈ G then (G.card : ℝ)⁻¹ else 0) / 2) = 1
    rw [← Finset.sum_div, Finset.sum_add_distrib, hg]
    simp [ne_of_gt hn]
  have hcross := finiteShannon_le_cross hp (fun a => (hqpos a).le) hp1 hq1
    (fun a ha => (ne_of_gt (hqpos a) ha).elim)
  have hm1 : 1 ≤ (G.card : ℝ) := by exact_mod_cast hG.card_pos
  have hlogm : 0 ≤ Real.log (G.card : ℝ) := Real.log_nonneg hm1
  have hterm a : -p a * Real.log (q a) ≤
      p a * (Real.log 2 + Real.log G.card) +
        (if a ∈ G then 0 else p a) * Real.log (Fintype.card α) := by
    by_cases ha : a ∈ G
    · have hlow : (G.card : ℝ)⁻¹ / 2 ≤ q a := by
        dsimp [q]
        rw [ite_eq_left ha]
        linarith [inv_pos.mpr hn]
      have hlog := Real.log_le_log (show 0 < (G.card : ℝ)⁻¹ / 2 by positivity) hlow
      rw [Real.log_div (by positivity) (by norm_num), Real.log_inv] at hlog
      rw [ite_eq_left ha]
      nlinarith [mul_le_mul_of_nonneg_left hlog (hp a)]
    · have hlow : (Fintype.card α : ℝ)⁻¹ / 2 ≤ q a := by
        simp [q, ha]
      have hlog := Real.log_le_log
        (show 0 < (Fintype.card α : ℝ)⁻¹ / 2 by positivity) hlow
      rw [Real.log_div (by positivity) (by norm_num), Real.log_inv] at hlog
      rw [ite_eq_right ha]
      nlinarith [mul_le_mul_of_nonneg_left hlog (hp a), mul_nonneg (hp a) hlogm]
  refine hcross.trans ((Finset.sum_le_sum fun a _ => hterm a).trans_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hp1, one_mul]

/-- If a collection of observation values misses at most `ε` of the
measure, its cardinality bounds the observation entropy. -/
theorem observationEntropy_le_good_card {Y α : Type*}
    [MeasurableSpace Y] [Fintype α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (G : Finset α) (hG : G.Nonempty) {ε : ℝ}
    (hbad : (∑ a, if a ∈ G then 0 else μ.real {y | P y = a}) ≤ ε) :
    observationEntropy μ P ≤ Real.log 2 + Real.log G.card +
      ε * Real.log (Fintype.card α) := by
  have hn : 1 ≤ Fintype.card α :=
    hG.card_pos.trans_le G.card_le_univ
  have hlog : 0 ≤ Real.log (Fintype.card α : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  exact (finiteShannon_le_good_card (fun a => μ.real {y | P y = a})
    (fun _ => measureReal_nonneg) (observation_distribution_sum μ P hP) G hG).trans
      (by gcongr)

/-- The exponential growth of a list of orbit names, together with its
exceptional mass, bounds the entropy rate of the observation. -/
theorem observationEntropyRate_le_of_good_names {Y α : Type*}
    [MeasurableSpace Y] [Fintype α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (G : ∀ N : ℕ, Finset (Fin N → α)) {a ε : ℝ}
    (hne : ∀ᶠ N : ℕ in atTop, (G N).Nonempty)
    (hbad : ∀ᶠ N : ℕ in atTop,
      (∑ w, if w ∈ G N then 0 else μ.real {y | orbitName T P N y = w}) ≤ ε)
    (hcard : ∀ᶠ N : ℕ in atTop, Real.log (G N).card ≤ a * N) :
    observationEntropyRate μ T P ≤ a + ε * Real.log (Fintype.card α) := by
  have hN : ∀ᶠ N : ℕ in atTop,
      observationEntropy μ (orbitName T P N) / (N : ℝ) ≤
        Real.log 2 / (N : ℝ) + (a + ε * Real.log (Fintype.card α)) := by
    filter_upwards [hne, hbad, hcard, eventually_ge_atTop (1 : ℕ)] with N hne hbad hcard hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hPN : ∀ w : Fin N → α, MeasurableSet {y | orbitName T P N y = w} :=
      orbitName_measurable_fiber hT.measurable hP N
    have h : observationEntropy μ (orbitName T P N) ≤
        Real.log 2 + Real.log (G N).card +
          ε * Real.log (Fintype.card (Fin N → α)) :=
      observationEntropy_le_good_card (α := Fin N → α) μ (orbitName T P N)
        hPN (G N) hne hbad
    have hlog : Real.log (Fintype.card (Fin N → α) : ℝ) =
        N * Real.log (Fintype.card α) := by
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
    rw [hlog] at h
    apply (div_le_iff₀ hn).mpr
    have hid : (Real.log 2 / (N : ℝ) + (a + ε * Real.log (Fintype.card α))) * N =
        Real.log 2 + a * N + ε * (N * Real.log (Fintype.card α)) := by
      field_simp
      ring
    rw [hid]
    linarith
  have hlim : Tendsto (fun N : ℕ => Real.log 2 / (N : ℝ) +
      (a + ε * Real.log (Fintype.card α))) atTop
      (𝓝 (a + ε * Real.log (Fintype.card α))) := by
    simpa only [zero_add] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => Real.log 2 / (N : ℝ)) atTop (𝓝 0)).add tendsto_const_nhds
  exact le_of_tendsto_of_tendsto (tendsto_observationEntropyRate μ hT P hP) hlim hN

end DukePrimeDegree

end OAI
