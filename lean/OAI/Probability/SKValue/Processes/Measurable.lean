import Mathlib
import OAI.Probability.SKValue.Evolution.TerminalError

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma IsDiffusion.measurable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    Measurable (X t) := by
  simpa only [Real.coe_toNNReal t ht.1, min_eq_left ht.2] using
    (hX.1 t.toNNReal).mono (W.filtration.le t.toNNReal) le_rfl

lemma drift_integral_bound (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ → ℝ) :
    |∫ s in (0 : ℝ)..t, γ.coeff s*gradient W γ s (x s)|≤∫ s in (0 : ℝ)..1, γ.cutoff s := by
  have he : (∫ s in (0 : ℝ)..t, γ.coeff s*gradient W γ s (x s)) =
      ∫ s in (0 : ℝ)..t, γ.cutoff s*gradient W γ s (x s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    change γ.coeff s*gradient W γ s (x s)=γ.cutoff s*gradient W γ s (x s)
    have hs' : s∈Ico (0 : ℝ) 1 := ⟨hs.1.le,hs.2.trans_le ht.2⟩
    rw [OrderParameter.cutoff, Set.indicator_of_mem hs']
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le ht.1
    (f := fun s ↦ γ.cutoff s*gradient W γ s (x s))
    (Eventually.of_forall (fun s hs ↦ by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (γ.cutoff_nonneg s)]
      exact (mul_le_mul_of_nonneg_left (gradient_bound W γ ⟨hs.1.le,hs.2.trans ht.2⟩ (x s))
        (γ.cutoff_nonneg s)).trans_eq (mul_one _)))
    (γ.cutoff_integrable.intervalIntegrable (a := 0) (b := t))
  have hm := intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := 1) le_rfl ht.1 ht.2
    (Eventually.of_forall (fun s ↦ γ.cutoff_nonneg s)) γ.cutoff_integrable.intervalIntegrable
  rw [Real.norm_eq_abs] at hb
  exact hb.trans hm

lemma IsDiffusion.drift_bound {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    ∀ᵐ ω ∂W.μ, ∀ t∈Icc (0 : ℝ) 1,
      |X t ω-W.B t.toNNReal ω|≤∫ s in (0 : ℝ)..1, γ.cutoff s := by
  filter_upwards [hX.2] with ω hω t ht
  rw [hω.2 t ht, add_sub_cancel_left]
  exact drift_integral_bound W γ ht (fun s ↦ X s ω)

lemma IsDiffusion.memLp {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1)
    {p : ℝ≥0∞} (hp : p≠∞) : MemLp (X t) p W.μ := by
  have hd : MemLp (fun ω ↦ X t ω-W.B t.toNNReal ω) p W.μ :=
    MemLp.of_bound ((hX.measurable ht).sub (W.measurable _).measurable).aestronglyMeasurable
      (∫ s in (0 : ℝ)..1, γ.cutoff s) (hX.drift_bound.mono (fun ω hω ↦ by
        simpa only [Real.norm_eq_abs] using hω t ht))
  have hb := (W.brownian.hasLaw_eval t.toNNReal).hasGaussianLaw.memLp hp
  convert hd.add hb using 1
  funext ω
  simp only [Pi.add_apply, sub_add_cancel]

lemma eventually_time_mem : ∀ᶠ t : ℝ in 𝓝[<] 1, t∈Icc (0 : ℝ) 1 := by
  filter_upwards [Ico_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with t ht
  exact ⟨ht.1,ht.2.le⟩

lemma IsDiffusion.ae_tendsto {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    ∀ᵐ ω ∂W.μ, Tendsto (fun t ↦ X t ω) (𝓝[<] (1 : ℝ)) (𝓝 (X 1 ω)) := by
  have ht : Tendsto (id : ℝ → ℝ) (𝓝[<] 1) (𝓝[Icc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds,eventually_time_mem⟩
  filter_upwards [hX.2] with ω hω
  exact Tendsto.comp (hω.1 1 (by norm_num : (1 : ℝ)∈Icc (0 : ℝ) 1)) ht

lemma IsDiffusion.L2_terminal {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    Tendsto (fun t ↦ ∫ ω, (X t ω-X 1 ω)^2 ∂W.μ) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let D (t : ℝ) (ω : W.Ω) := X t ω-W.B t.toNNReal ω
  let G := ∫ s in (0 : ℝ)..1, γ.cutoff s
  have hG : 0≤G := intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun s ↦ γ.cutoff_nonneg s)
  have hD (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : MemLp (D t) 2 W.μ :=
    (hX.memLp ht (by norm_num)).sub ((W.brownian.hasLaw_eval t.toNNReal).hasGaussianLaw.memLp_two)
  have hD1 := hD 1 (by norm_num)
  have hDb : ∀ᵐ ω ∂W.μ, ∀ t∈Icc (0 : ℝ) 1, |D t ω|≤G := hX.drift_bound
  have hDC : ∀ᵐ ω ∂W.μ, Tendsto (fun t ↦ D t ω) (𝓝[<] (1 : ℝ)) (𝓝 (D 1 ω)) := by
    filter_upwards [hX.ae_tendsto,W.brownian.cont] with ω hω hBω
    exact hω.sub ((hBω.comp continuous_real_toNNReal).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hDL : Tendsto (fun t ↦ ∫ ω, (D t ω-D 1 ω)^2 ∂W.μ)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := W.μ) (l := 𝓝[<] (1 : ℝ)) (F := fun t ω ↦ (D t ω-D 1 ω)^2) (f := fun _ ↦ (0 : ℝ))
      (fun _ ↦ 4*G^2) ?_ ?_ (integrable_const (4*G^2)) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [eventually_time_mem] with t ht
      exact ((hD t ht).sub hD1).aestronglyMeasurable.aemeasurable.pow_const 2 |>.aestronglyMeasurable
    · filter_upwards [eventually_time_mem] with t ht
      filter_upwards [hDb] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h0 := abs_le.mp (hω t ht)
      have h1 := abs_le.mp (hω 1 (by norm_num))
      nlinarith [sq_nonneg (D t ω-D 1 ω), sq_nonneg (G-(D t ω-D 1 ω)/2),
        sq_nonneg (G+(D t ω-D 1 ω)/2), mul_nonneg (show 0≤2*G-(D t ω-D 1 ω) by linarith)
          (show 0≤2*G+(D t ω-D 1 ω) by linarith)]
    · filter_upwards [hDC] with ω hω
      simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ)≠0)] using (hω.sub (tendsto_const_nhds (x := D 1 ω))).pow 2
  have hb : ∀ t∈Icc (0 : ℝ) 1,
      (∫ ω, (X t ω-X 1 ω)^2 ∂W.μ) ≤
      2*(∫ ω, (D t ω-D 1 ω)^2 ∂W.μ)+2*(1-t) := by
    intro t ht
    have hxint := ((hX.memLp ht (by norm_num : (2 : ℝ≥0∞)≠∞)).sub
      (hX.memLp (by norm_num : (1 : ℝ)∈Icc (0 : ℝ) 1) (by norm_num))).integrable_sq
    have hdint : Integrable (fun ω ↦ (D t ω-D 1 ω)^2) W.μ := ((hD t ht).sub hD1).integrable_sq
    have hbint := (brownian_increment_memLp W t).integrable_sq
    calc
      _ ≤ ∫ ω, 2*(D t ω-D 1 ω)^2+2*(W.B 1 ω-W.B t.toNNReal ω)^2 ∂W.μ := by
        apply integral_mono hxint ((hdint.const_mul 2).add (hbint.const_mul 2))
        intro ω
        dsimp only [D,Pi.add_apply,Pi.sub_apply]
        simp only [Real.toNNReal_one]
        nlinarith [sq_nonneg (X t ω-W.B t.toNNReal ω-(X 1 ω-W.B 1 ω)+(W.B 1 ω-W.B t.toNNReal ω))]
      _ = _ := by
        rw [integral_add (hdint.const_mul 2) (hbint.const_mul 2), integral_const_mul,
          integral_const_mul, brownian_increment_second W ht]
  apply squeeze_zero' (Eventually.of_forall (fun t ↦ integral_nonneg (fun ω ↦ sq_nonneg _)))
    (eventually_time_mem.mono (fun t ht ↦ hb t ht))
  simpa only [sub_self, mul_zero, add_zero,id_eq] using
    (hDL.const_mul 2).add (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (id : ℝ → ℝ) (𝓝[<] 1) (𝓝 1))).const_mul 2)

end SKValue

end

end OAI
