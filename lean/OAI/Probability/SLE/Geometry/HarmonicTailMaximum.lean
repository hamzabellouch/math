import OAI.Probability.SLE.Geometry.HarmonicLimitData

namespace OAI

/-! The maximal error after a compact localization stop is bounded by
the L1 error to the bounded harmonic terminal variable. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target
namespace SmoothDomainExhaustion
variable {U : Set (ℝ×ℝ)} (e : SmoothDomainExhaustion U 0)

def harmonicTailEvent (T : ℝ≥0) (u : ℝ×ℝ → ℝ) (n : ℕ) (ε : ℝ≥0) : Set (Driver×Driver) :=
  {b | ∃ m : ℕ, ∃ t∈Icc (e.stop T n b) (e.stop T (n+m) b),
    (ε:ℝ) < |u (planarWiener t b)-u (planarWiener (e.stop T n b) b)|}

theorem harmonic_tail_maximal
    (W : WienerLaw) (hW : IsWiener W) (T : ℝ≥0) (hU : IsOpen U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (C : ℝ≥0) (huC : ∀ z∈U, |u z|≤C)
    (Y : Driver×Driver → ℝ)
    (hY : ∀ᵐ b ∂W.prod W,
      Tendsto (fun n => u (planarWiener (e.stop T n b) b)) atTop (𝓝 (Y b)))
    (n : ℕ) (ε : ℝ≥0) :
    ε*(W.prod W) (e.harmonicTailEvent T u n ε) ≤
      ENNReal.ofReal (∫ b, |Y b-u (planarWiener (e.stop T n b) b)| ∂W.prod W) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let X (j : ℕ) (b : Driver×Driver) := u (planarWiener (e.stop T j b) b)
  have hM := e.harmonic_stopped_martingale W hW T hU u hu hhar C huC
  have hXm (j) : Measurable (X j) := ((hM.1 j).mono ((e.stopFiltration T).le j)).measurable
  have hXb (j b) : |X j b|≤C := huC _ (e.stop_mem_domain T j b _ le_rfl)
  let A (m : ℕ) : Set (Driver×Driver) :=
    {b | ∃ t∈Icc (e.stop T n b) (e.stop T (n+m) b), (ε:ℝ) < |u (planarWiener t b)-X n b|}
  have hAm : Monotone A := by
    intro i j hij b hb
    obtain ⟨t,ht,hε⟩ := hb
    exact ⟨t,⟨ht.1,ht.2.trans (e.stop_monotone T b (Nat.add_le_add_left hij n))⟩,hε⟩
  have he : e.harmonicTailEvent T u n ε=⋃ m, A m := by
    ext b
    simp only [harmonicTailEvent,A,X,mem_iUnion,mem_ofPred_eq]
  have hbound (m) : ε*(W.prod W) (A m) ≤
      ENNReal.ofReal (∫ b, |X (n+m) b-X n b| ∂W.prod W) :=
    harmonic_path_maximal W hW U (tsupport (e.cutoff (n+m))) hU
      (e.compact (n+m)) (e.supported (n+m)) u hu hhar
      (e.stop T n) (e.stop T (n+m)) (e.stop_stopping T n) (e.stop_stopping T (n+m))
      (fun b => e.stop_monotone T b (Nat.le_add_right n m))
      T (e.stop_le T (n+m)) (e.stop_mem_support T (n+m)) ε
  have hright : Tendsto (fun m => ∫ b, |X (n+m) b-X n b| ∂W.prod W) atTop
      (𝓝 (∫ b, |Y b-X n b| ∂W.prod W)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (2:ℝ)*C)
      (fun m => ((hXm (n+m)).sub (hXm n)).abs.aestronglyMeasurable) (integrable_const _)
    · intro m
      exact Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs,abs_abs]
        exact (abs_sub _ _).trans (by linarith [hXb (n+m) b,hXb n b])
    · filter_upwards [hY] with b hb
      have hh := hb.comp (tendsto_add_atTop_nat n)
      simpa only [Function.comp_apply,Pi.sub_apply,X,Nat.add_comm] using (hh.sub_const (X n b)).abs
  have hleft := (ENNReal.continuous_const_mul (ENNReal.coe_ne_top (r := ε))).continuousAt.tendsto.comp
    (tendsto_measure_iUnion_atTop (μ := W.prod W) hAm)
  rw [he]
  exact le_of_tendsto_of_tendsto hleft (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hright)
    (Eventually.of_forall hbound)

end SmoothDomainExhaustion
end SLEExactGauge

end

end OAI
