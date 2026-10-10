import OAI.Geometry.RCD.Transport.BoundedEntropyClosed
import OAI.Geometry.RCD.Transport.CompressedPlanMixture

namespace OAI

/-! # An entropy gap cannot persist immediately after a common initial marginal -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem initial_entropy_obstruction (μ : Measure X) [SigmaFinite μ]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (π₀ π₁ : Measure C(Time,X)) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc₀ : ∀ t : Time, π₀.map (fun γ => γ t) ≤ C • μ)
    (hc₁ : ∀ t : Time, π₁.map (fun γ => γ t) ≤ C • μ)
    (hs₀ : ∀ t : Time, ∀ᵐ x ∂π₀.map (fun γ => γ t), x ∈ B)
    (hs₁ : ∀ t : Time, ∀ᵐ x ∂π₁.map (fun γ => γ t), x ∈ B)
    {A : ℝ}
    (hch₀ : EntropyChord (fun t => boltzmannEntropy μ (π₀.map (fun γ => γ t))) A)
    (hch₁ : EntropyChord (fun t => boltzmannEntropy μ (π₁.map (fun γ => γ t))) A)
    (hinit : π₀.map (fun γ => γ 0)=π₁.map (fun γ => γ 0))
    (hsep : ∀ t : Time, 0 < (t:ℝ) → (t:ℝ) < 1 →
      π₀.map (fun γ => γ t) ⟂ₘ π₁.map (fun γ => γ t)) : False := by
  let π := (2:ℝ≥0∞)⁻¹ • (π₀+π₁)
  let : IsProbabilityMeasure π := ⟨by
    change (2:ℝ≥0∞)⁻¹*(π₀ univ+π₁ univ)=1
    simp only [measure_univ]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩
  let E₀ := fun t : Time => boltzmannEntropy μ (π₀.map (fun γ => γ t))
  let E₁ := fun t : Time => boltzmannEntropy μ (π₁.map (fun γ => γ t))
  let a := fun t : Time => (1-(t:ℝ))*E₀ 0+(t:ℝ)*(E₀ 1+E₁ 1)/2+
    A*(t:ℝ)*(1-(t:ℝ))-Real.log 2
  have ha : Continuous a := by
    dsimp only [a]
    fun_prop
  have hc (t : Time) : π.map (fun γ => γ t) ≤ C • μ :=
    half_mixture_compression μ π₀ π₁ hc₀ hc₁ t
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B := by
    rw [show π=(2:ℝ≥0∞)⁻¹ • (π₀+π₁) from rfl,half_mixture_map_eval]
    exact (ae_add_measure_iff.mpr ⟨hs₀ t,hs₁ t⟩).filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hb (t : Time) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
      boltzmannEntropy μ (π.map (fun γ => γ t)) ≤ a t := by
    have he : timeSegment 0 1 t=t := by ext; simp [timeSegment]
    have hh₀ := hch₀ 0 1 t
    have hh₁ := hch₁ 0 1 t
    simp only [he,show ((0:Time):ℝ)=0 from rfl,show ((1:Time):ℝ)=1 from rfl] at hh₀ hh₁
    have heinit : E₁ 0=E₀ 0 := congrArg (boltzmannEntropy μ) hinit.symm
    have heq : boltzmannEntropy μ (π.map (fun γ => γ t))=(E₀ t+E₁ t)/2-Real.log 2 := by
      rw [show π=(2:ℝ≥0∞)⁻¹ • (π₀+π₁) from rfl,half_mixture_map_eval]
      exact boltzmannEntropy_half_mixture μ _ _
        (Measure.absolutelyContinuous_of_le_smul (hc₀ t))
        (Measure.absolutelyContinuous_of_le_smul (hc₁ t)) (hsep t ht0 ht1)
        (entropy_integrable_of_bounded_support μ _ hC (hc₀ t) hB (hs₀ t))
        (entropy_integrable_of_bounded_support μ _ hC (hc₁ t) hB (hs₁ t))
    change E₀ t ≤ (1-(t:ℝ))*E₀ 0+(t:ℝ)*E₀ 1+A*(t:ℝ)*(1-(t:ℝ))*|0-1|^2 at hh₀
    change E₁ t ≤ (1-(t:ℝ))*E₁ 0+(t:ℝ)*E₁ 1+A*(t:ℝ)*(1-(t:ℝ))*|0-1|^2 at hh₁
    rw [heinit] at hh₁
    simp only [zero_sub,abs_neg,abs_one,one_pow,mul_one] at hh₀ hh₁
    rw [heq]
    dsimp only [a]
    linarith
  let u : ℕ → Time := fun j => ⟨(1/((j:ℝ)+1))/2,by
    constructor
    · positivity
    · have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1)
        (by have := Nat.cast_nonneg (α:=ℝ) j; linarith : (1:ℝ)≤j+1)
      linarith⟩
  have hu0 (j : ℕ) : 0 < ((u j):ℝ) := by dsimp [u]; positivity
  have hu1 (j : ℕ) : ((u j):ℝ) < 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1)
      (by have := Nat.cast_nonneg (α:=ℝ) j; linarith : (1:ℝ)≤j+1)
    change (1/((j:ℝ)+1))/2<1
    linarith
  have hu : Tendsto u atTop (𝓝 0) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun j : ℕ => (1/((j:ℝ)+1))/2) atTop (𝓝 (0:ℝ))
    simpa only [zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).div_const 2
  have hzero := bounded_entropy_time_limit μ hB π hC hc hs a ha hu (fun j => hb (u j) (hu0 j) (hu1 j))
  have he0 : π.map (fun γ => γ 0)=π₀.map (fun γ => γ 0) :=
    half_mixture_eval_eq π₀ π₁ 0 hinit
  rw [he0] at hzero
  change E₀ 0 ≤ a 0 at hzero
  simp only [a,show ((0:Time):ℝ)=0 from rfl,sub_zero,one_mul,zero_mul,add_zero,mul_zero] at hzero
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end RegularPointCoordinates

end

end OAI
