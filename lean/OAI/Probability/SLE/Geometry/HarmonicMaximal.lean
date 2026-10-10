import OAI.Probability.SLE.Stochastic.PlanarHarmonicSampling

namespace OAI

/-! The finite maximal estimate used to control a harmonic test between
two of the actual domain-localization stops. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma martingale_abs_sub_initial {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ) :
    Submartingale (fun n b => |X n b-X 0 b|) ℱ μ := by
  have hM : Martingale (fun n b => X n b-X 0 b) ℱ μ :=
    hX.sub (martingale_const_fun ℱ μ (hX.1 0) (hX.integrable 0))
  refine ⟨fun n => by simpa only [Real.norm_eq_abs] using (hM.1 n).norm,
    fun i j hij => ?_, fun n => (hM.integrable n).abs⟩
  filter_upwards [hM.2 i j hij,
    abs_condExp_ae_le_condExp_abs (μ := μ) (m := ℱ i) (fun b => X j b-X 0 b)]
    with b hb hle
  change |μ[(fun b => X j b-X 0 b) | ℱ i] b| ≤
    μ[(fun b => |X j b-X 0 b|) | ℱ i] b at hle
  rwa [hb] at hle

lemma martingale_finite_maximal {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ) (ε : ℝ≥0) (N : ℕ) :
    ε * μ {b | ∃ k ≤ N, (ε:ℝ) ≤ |X k b-X 0 b|} ≤
      ENNReal.ofReal (∫ b, |X N b-X 0 b| ∂μ) := by
  have hm := martingale_abs_sub_initial hX
  have hh := maximal_ineq hm (fun n b => abs_nonneg _) (ε := ε) N
  have he : {b | (ε:ℝ) ≤ (Finset.range (N+1)).sup' Finset.nonempty_range_add_one
      (fun k => |X k b-X 0 b|)}={b | ∃ k ≤ N, (ε:ℝ) ≤ |X k b-X 0 b|} := by
    ext b
    simp only [mem_ofPred_eq,Finset.le_sup'_iff,Finset.mem_range,Nat.lt_succ_iff]
  rw [he] at hh
  exact hh.trans (ENNReal.ofReal_le_ofReal (setIntegral_le_integral
    (hm.integrable N) (Eventually.of_forall fun b => abs_nonneg _)))

end SLEExactGauge

end

end OAI
