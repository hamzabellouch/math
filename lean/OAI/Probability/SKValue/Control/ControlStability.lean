import Mathlib
import OAI.Probability.SKValue.Equations.LipschitzCompMemLpFinite
import OAI.Probability.SKValue.Control.Controls
import OAI.Probability.SKValue.Evolution.BoundedSmooth

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma controlAccum_L1_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) (n : ℕ) (ω : Ω) :
    |controlAccum γ α n T ω|≤∫ s in (0 : ℝ)..T, |γ s| := by
  have hint := controlAccum_integrand_intervalIntegrable hα hαb hγ hi hT n ω
  apply (intervalIntegral.abs_integral_le_integral_abs hT).trans
  apply intervalIntegral.integral_mono_on hT hint.abs hi.abs
  intro s hs
  rw [abs_mul,abs_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) (hαb _ _)) (abs_nonneg _)).trans_eq (mul_one _)

lemma controlAccum_memLp_of_interval {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Filtration ℝ≥0 m}
    {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (controlAccum γ α n T) p μ := by
  apply MemLp.of_bound ((controlAccum_measurable hα hγ n hT).mono (f.le _) le_rfl).aestronglyMeasurable
    (∫ s in (0 : ℝ)..T, |γ s|)
  exact Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (controlAccum_L1_bound hα hαb hγ hi hT n ω))

lemma controlAccum_sub {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ η : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T)
    (hT : 0≤T) (n : ℕ) (ω : Ω) :
    controlAccum γ α n T ω-controlAccum η α n T ω=controlAccum (fun s ↦ γ s-η s) α n T ω := by
  have h1 := controlAccum_integrand_intervalIntegrable hα hαb hγ hiγ hT n ω
  have h2 := controlAccum_integrand_intervalIntegrable hα hαb hη hiη hT n ω
  simp only [controlAccum,sub_mul,intervalIntegral.integral_sub h1 h2]

lemma controlAccum_difference_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ η : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T)
    (hT : 0≤T) (n : ℕ) (ω : Ω) :
    |controlAccum γ α n T ω-controlAccum η α n T ω|≤∫ s in (0 : ℝ)..T, |γ s-η s| := by
  rw [controlAccum_sub hα hαb hγ hη hiγ hiη hT]
  exact controlAccum_L1_bound hα hαb (hγ.sub hη) (hiγ.sub hiη) hT n ω

noncomputable def elapsedPayoff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℝ) (ψ γ : ℝ → ℝ) (T x : ℝ) (α : ℝ≥0 → Ω → ℝ) : ℝ :=
  ∫ ω, ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω ∂μ

lemma elapsedPayoff_integrable {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Filtration ℝ≥0 m}
    {α : ℝ≥0 → Ω → ℝ} {ψ γ : ℝ → ℝ} {T x : ℝ} {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ)
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) :
    Integrable (fun ω ↦ ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω) μ := by
  have h1 := controlAccum_memLp_of_interval (μ := μ) hα hαb hγ hi hT 1 2
  have h2 := controlAccum_memLp_of_interval (μ := μ) hα hαb hγ hi hT 2 2
  have hs := lipschitz_comp_memLp_finite hψ (((memLp_const x).add hZ).add h1)
  exact (hs.integrable (by norm_num)).sub ((h2.integrable (by norm_num)).const_mul _)

lemma elapsedPayoff_difference_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Filtration ℝ≥0 m}
    {α : ℝ≥0 → Ω → ℝ} {ψ χ γ η : ℝ → ℝ} {T x ε : ℝ} {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    (hε : ∀ y, |ψ y-χ y|≤ε) (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T) (hT : 0≤T) :
    |elapsedPayoff μ Z ψ γ T x α-elapsedPayoff μ Z χ η T x α|≤
      ε+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s-η s|) := by
  let D := ∫ s in (0 : ℝ)..T, |γ s-η s|
  have hp := elapsedPayoff_integrable hZ hψ hα hαb hγ hiγ hT (x := x)
  have hq := elapsedPayoff_integrable hZ hχ hα hαb hη hiη hT (x := x)
  unfold elapsedPayoff
  rw [←integral_sub hp hq]
  apply (abs_integral_le_integral_abs).trans
  have hb : ∀ ω,
      |(ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω)-
        (χ (x+Z ω+controlAccum η α 1 T ω)-(1/2 : ℝ)*controlAccum η α 2 T ω)|≤ε+(3/2 : ℝ)*D := by
    intro ω
    have h1 := controlAccum_difference_bound hα hαb hγ hη hiγ hiη hT 1 ω
    have h2 := controlAccum_difference_bound hα hαb hγ hη hiγ hiη hT 2 ω
    have hl := hχ.dist_le_mul (x+Z ω+controlAccum γ α 1 T ω) (x+Z ω+controlAccum η α 1 T ω)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,add_sub_add_left_eq_sub] at hl
    have htri := abs_sub_le (ψ (x+Z ω+controlAccum γ α 1 T ω))
      (χ (x+Z ω+controlAccum γ α 1 T ω)) (χ (x+Z ω+controlAccum η α 1 T ω))
    have he := hε (x+Z ω+controlAccum γ α 1 T ω)
    have hcost : |(1/2 : ℝ)*controlAccum γ α 2 T ω-(1/2 : ℝ)*controlAccum η α 2 T ω|≤(1/2 : ℝ)*D := by
      rw [←mul_sub,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have htri2 := norm_sub_le (ψ (x+Z ω+controlAccum γ α 1 T ω)-χ (x+Z ω+controlAccum η α 1 T ω))
      ((1/2 : ℝ)*controlAccum γ α 2 T ω-(1/2 : ℝ)*controlAccum η α 2 T ω)
    simp only [Real.norm_eq_abs] at htri2
    have heq : (ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω)-
        (χ (x+Z ω+controlAccum η α 1 T ω)-(1/2 : ℝ)*controlAccum η α 2 T ω)=
        (ψ (x+Z ω+controlAccum γ α 1 T ω)-χ (x+Z ω+controlAccum η α 1 T ω))-
        ((1/2 : ℝ)*controlAccum γ α 2 T ω-(1/2 : ℝ)*controlAccum η α 2 T ω) := by ring
    rw [heq]
    dsimp only [D] at *
    linarith
  exact (integral_mono (hp.sub hq).abs (integrable_const _) hb).trans_eq (by simp [D])

end SKValue

end

end OAI
