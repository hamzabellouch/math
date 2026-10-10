import OAI.Probability.SLE.Mass.LevelApproximationTests
import OAI.Probability.SLE.Mass.L2ConvexTails

namespace OAI

/-! Uniform Hilbert bounds and one common deterministic convex extraction
for the actual finite-level measure tests. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

lemma eLpNorm_toReal_two_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Ω → ℝ≥0∞) (hA : Measurable A) (M : ℝ≥0∞)
    (hM : (∫⁻ ω, A ω ^ 2 ∂P) ≤ M) :
    eLpNorm (fun ω => (A ω).toReal) 2 P ≤ M ^ (1/2 : ℝ) := by
  have hn (ω : Ω) : ‖(A ω).toReal‖ₑ ≤ A ω := by
    rw [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  have hi : (∫⁻ ω, ‖(A ω).toReal‖ₑ ^ 2 ∂P) ≤ M :=
    (lintegral_mono (fun ω => pow_le_pow_left' (hn ω) 2)).trans hM
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    ENNReal.ofNat_ne_top hA.ennreal_toReal.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofNat,ENNReal.rpow_two] using
    ENNReal.rpow_le_rpow hi (by norm_num : (0 : ℝ) ≤ 1/2)

lemma memLp_toReal_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Ω → ℝ≥0∞) (hA : Measurable A) (M : ℝ≥0∞) (hM : M < ⊤)
    (hAM : (∫⁻ ω, A ω ^ 2 ∂P) ≤ M) :
    MemLp (fun ω => (A ω).toReal) 2 P := by
  apply lt_of_le_of_lt (eLpNorm_toReal_two_le P A hA M hAM)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne

lemma norm_toLp_toReal_two_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Ω → ℝ≥0∞) (hA : Measurable A) (M : ℝ≥0∞) (hM : M < ⊤)
    (hAM : (∫⁻ ω, A ω ^ 2 ∂P) ≤ M)
    (hLp : MemLp (fun ω => (A ω).toReal) 2 P) :
    ‖hLp.toLp (fun ω => (A ω).toReal)‖ ≤ (M ^ (1/2 : ℝ)).toReal := by
  rw [Lp.norm_toLp]
  exact ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hM.ne)
    (eLpNorm_toReal_two_le P A hA M hAM)

theorem exists_common_levelApproximation_test_limits
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : ℕ → Set ℂ) (hK : ∀ j, IsCompact (K j)) (hKH : ∀ j, K j ⊆ upperHalfPlane)
    (f : ℕ → ℂ → ℝ≥0∞) (hfm : ∀ j, Measurable (f j))
    (C : ℕ → ℝ≥0∞) (hC : ∀ j, C j < ⊤)
    (hf : ∀ j z, z ∈ K j → f j z ≤ C j) (hz : ∀ j z, z ∉ K j → f j z = 0)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (t : ℕ → ℝ≥0∞) :
    ∃ x : ℕ → Lp ℝ 2 P, ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧
      (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ᵐ ω ∂P, ∀ j, Tendsto (fun n => ∑ i ∈ s n, w n i *
        (levelApproximationTest κ B γ G (u (n+i)) (t j) (f j) ω).toReal)
        atTop (𝓝 (x j ω))) := by
  let A (n j : ℕ) (ω : Ω) := levelApproximationTest κ B γ G (u n) (t j) (f j) ω
  have hAm (n j : ℕ) : Measurable (A n j) :=
    levelApproximationTest_measurable hm hBc κ (u n) (hu n) γ G F hw (t j) (f j) (hfm j)
  choose M hM hbound using fun j => uniform_levelApproximationTest_moments hB hm hBm hBc hB0
    hκ hκ8 γ G F hw hgrowth (K j) (hK j) (hKH j) (f j) (C j) (hC j) (hf j) (hz j) 2
  have hLp (n j : ℕ) : MemLp (fun ω => (A n j ω).toReal) 2 P :=
    memLp_toReal_two P (A n j) (hAm n j) (M j) (hM j) (hbound j (u n) (hu n) (t j))
  have hnorm (j : ℕ) : ∃ D : ℝ, ∀ n, ‖(hLp n j).toLp (fun ω => (A n j ω).toReal)‖ ≤ D := by
    refine ⟨(M j ^ (1/2 : ℝ)).toReal,fun n => ?_⟩
    exact norm_toLp_toReal_two_le P (A n j) (hAm n j) (M j) (hM j)
      (hbound j (u n) (hu n) (t j)) (hLp n j)
  obtain ⟨x,s,w,hw₀,hw₁,_,hconv⟩ := exists_randomVariable_convex_tail_limit
    (fun n j ω => (A n j ω).toReal) hLp hnorm
  exact ⟨x,s,w,hw₀,hw₁,hconv⟩

end SLEExactGauge.Multipoint

end

end OAI
