import OAI.Analysis.IrrationalRotation.Sampling.SamplingTestTrialBridge

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace Invariant233.SamplingTests

theorem exists_character_stage_of_moment_budget
    {ι : Type*} [Fintype ι] {θ : ℝ} (hθ : Irrational θ)
    {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 2 < N)
    (samples : ι → Finset ℕ) (hpositive : ∀ r, ∀ n ∈ samples r, 0 < n)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ≥0∞}
    (hmoment : ∀ r endpoint, (∫⁻ phase,
      TrialSampling.squaredError m (samples r) endpoint phase ∂TrialSampling.phaseLaw m N) ≤ δ)
    (hbudget : ENNReal.ofReal (ProductPhases.failureBound m) +
      (2 * Fintype.card ι : ℝ≥0∞) * (δ / ENNReal.ofReal (ρ ^ 2)) < 1)
    (R : ℝ) {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, q i ∣ q (i + 1)) ∧
      (∀ i < m, R ≤ (q (i + 1) : ℝ) / q i) ∧
      (∀ i : Fin m, Int.fract ((q (i.val + 1) : ℝ) * θ) ∈ Ioo (1/N) (2/N)) ∧
      ProductPhases.strictLargePhaseCondition Finset.univ N
        (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∧
      ∀ r endpoint, eLpNorm (fun x : Circle =>
        TrialSampling.average m (samples r) endpoint
          (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
          (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 circleMeasure <
            ENNReal.ofReal ρ := by
  classical
  have hNpos : 0 < N := by linarith
  have hm100 : (100 : ℝ) ≤ m := by
    have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨τ, hbox, hnonres, hspread, htests⟩ :=
    TrialSampling.exists_strict_trials_of_moment_budget m hNpos
      hm100
      (Finset.univ : Finset ι) samples
      (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hρ))) ENNReal.ofReal_ne_top
      (fun r _ endpoint => hmoment r endpoint) (by simpa using hbudget)
  have hτ : ∀ i, 0 < τ i ∧ τ i < 1 := by
    intro i
    exact ⟨(one_div_pos.mpr hNpos).trans (hbox i).1,
      (hbox i).2.trans ((div_lt_one hNpos).mpr hN)⟩
  have hphase : ∀ r, ∀ n ∈ samples r, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0 := by
    intro r n hn i
    exact hnonres i (n : ℤ) (by exact_mod_cast (hpositive r n hn).ne')
  let U : Set (Fin m → ℝ) := {a | (∀ i, a i ∈ Ioo (1/N) (2/N)) ∧
    ProductPhases.strictLargePhaseCondition Finset.univ N a}
  have hU : U ∈ 𝓝 τ := by
    have hb : ∀ᶠ a in 𝓝 τ, ∀ i : Fin m, a i ∈ Ioo (1/N) (2/N) := by
      apply Filter.eventually_all.mpr
      intro i
      exact (continuous_apply i).continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (hbox i))
    have hs := ProductPhases.eventually_strictLargePhaseCondition
      (Finset.univ : Finset (Fin m)) (by simpa using (show 0 < m by omega)) hNpos τ hspread
    exact hb.and hs
  obtain ⟨q, hzero, hpos, hstrict, hdiv, hgap, hUq, hnorm⟩ :=
    exists_character_sampling_block_L2 hθ hm samples τ hτ hphase
      (fun _ _ => ρ) (fun _ _ => hρ) (fun r e => htests r (Finset.mem_univ r) e)
      U hU R hq₀
  exact ⟨q, hzero, hpos, hstrict, hdiv, hgap, hUq.1, hUq.2, hnorm⟩

end Invariant233.SamplingTests

end

end OAI
