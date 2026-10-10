import Mathlib
import OAI.Probability.SKValue.GroundState.GumbelMax

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal
namespace SKValueG

noncomputable def empiricalMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range (n+1), X i ω)/(n+1 : ℝ)

lemma empiricalMean_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} (hi : ∀ i, Integrable (X i) μ) (n : ℕ) :
    Integrable (empiricalMean X n) μ :=
  (integrable_finsetSum _ (fun i _ ↦ hi i)).div_const _

lemma integral_empiricalMean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} (hi : ∀ i, Integrable (X i) μ)
    (he : ∀ i, (∫ ω, X i ω ∂μ)=∫ ω, X 0 ω ∂μ) (n : ℕ) :
    (∫ ω, empiricalMean X n ω ∂μ)=∫ ω, X 0 ω ∂μ := by
  simp only [empiricalMean]
  rw [integral_div,integral_finsetSum _ (fun i _ ↦ hi i)]
  simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  have hn : (n : ℝ)+1≠0 := by positivity
  field_simp

lemma empirical_log_lower {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hp : ∀ i, 0<X i ω) :
    empiricalMean (fun i ω ↦ Real.log (X i ω)) n ω ≤ Real.log (empiricalMean X n ω) := by
  have h := log_mean_lower (fun i : Fin (n+1) ↦ X i ω) (fun i ↦ hp i)
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ Real.log (X i ω)),
    Fin.sum_univ_eq_sum_range (fun i ↦ X i ω)] at h
  simpa only [Fintype.card_fin,empiricalMean,Nat.cast_add,Nat.cast_one] using h

lemma empiricalMean_pos {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hp : ∀ i, 0<X i ω) : 0<empiricalMean X n ω := by
  apply div_pos
  · exact Finset.sum_pos (fun i _ ↦ hp i) (Finset.nonempty_range_iff.mpr (by omega))
  · positivity

theorem expected_log_empiricalMean_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hi : Integrable (X 0) μ) (hl : Integrable (fun ω ↦ Real.log (X 0 ω)) μ)
    (hp : ∀ i, ∀ᵐ ω ∂μ, 0<X i ω)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun n ↦ ∫ ω, Real.log (empiricalMean X n ω) ∂μ)
      atTop (𝓝 (Real.log (∫ ω, X 0 ω ∂μ))) := by
  let Y := fun i ω ↦ Real.log (X i ω)
  have hiX (i) : Integrable (X i) μ := (hid i).integrable_iff.mpr hi
  have hidY (i) : IdentDistrib (Y i) (Y 0) μ μ := (hid i).comp Real.measurable_log
  have hiY (i) : Integrable (Y i) μ := (hidY i).integrable_iff.mpr hl
  have hpall : ∀ᵐ ω ∂μ, ∀ i, 0<X i ω := ae_all_iff.mpr hp
  have hiA (n) := empiricalMean_integrable hiX n
  have hiB (n) := empiricalMean_integrable hiY n
  have hpos : 0<∫ ω, X 0 ω ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae ((hp 0).mono (fun _ h ↦ h.le)) hi).mpr (by
      have hs : Function.support (X 0) =ᵐ[μ] univ := (hp 0).mono (fun ω hω ↦ by
        apply propext; change X 0 ω≠0 ↔ True; simp [hω.ne'])
      rw [measure_congr hs]; simp)
  have hlogmeas (n) : AEStronglyMeasurable (fun ω ↦ Real.log (empiricalMean X n ω)) μ :=
    (Real.measurable_log.comp_aemeasurable (hiA n).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hilog (n) : Integrable (fun ω ↦ Real.log (empiricalMean X n ω)) μ := by
    apply (((hiA n).sub (integrable_const 1)).abs.add (hiB n).abs).mono' (hlogmeas n)
    filter_upwards [hpall] with ω hω
    have hpA := empiricalMean_pos X n ω hω
    have hlo := empirical_log_lower X n ω hω
    have hup := log_tangent_bound hpA (show (0 : ℝ)<1 by norm_num)
    simp only [div_one,Real.log_one,add_zero] at hup
    change |Real.log (empiricalMean X n ω)| ≤ |empiricalMean X n ω-1|+|empiricalMean Y n ω|
    apply abs_le.mpr
    constructor
    · have hh := neg_abs_le (empiricalMean Y n ω)
      have hh' := abs_nonneg (empiricalMean X n ω-1)
      change empiricalMean Y n ω ≤ _ at hlo
      linarith
    · have hh := le_abs_self (empiricalMean X n ω-1)
      have hh' := abs_nonneg (empiricalMean Y n ω)
      linarith
  let F := fun n ω ↦ Real.log (empiricalMean X n ω)-empiricalMean Y n ω
  have hiF (n) : Integrable (F n) μ := (hilog n).sub (hiB n)
  have hFnonneg (n) : ∀ᵐ ω ∂μ, 0≤F n ω :=
    hpall.mono (fun ω hω ↦ sub_nonneg.mpr (empirical_log_lower X n ω hω))
  let c := Real.log (∫ ω, X 0 ω ∂μ)-(∫ ω, Y 0 ω ∂μ)
  have hc : 0≤c := sub_nonneg.mpr (integral_log_le_log_integral hi hl (hp 0))
  have hAX := strong_law_ae_real X hi hind hid
  have hBY := strong_law_ae_real Y hl
    (fun i j hij ↦ (hind hij).comp Real.measurable_log Real.measurable_log) hidY
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ F n ω) atTop (𝓝 c) := by
    filter_upwards [hAX,hBY] with ω hX hY
    have hx := (hX.comp (tendsto_add_atTop_nat 1)).log hpos.ne'
    have hy := hY.comp (tendsto_add_atTop_nat 1)
    simpa only [F,c,empiricalMean,Function.comp_def,Nat.cast_add,Nat.cast_one] using hx.sub hy
  have hiC (n) : Integrable (fun ω ↦ min (F n ω) c) μ := (hiF n).inf (integrable_const c)
  have htrunc := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ c)
    (fun n ↦ (hiC n).aestronglyMeasurable) (integrable_const c)
    (fun n ↦ (hFnonneg n).mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min hω hc)]
      exact min_le_right _ _))
    (hlim.mono (fun ω hω ↦ by simpa only [min_self] using hω.min (tendsto_const_nhds (x := c))))
  have htrunc' : Tendsto (fun n ↦ ∫ ω, min (F n ω) c ∂μ) atTop (𝓝 c) := by simpa using htrunc
  have hIntegral (n) : (∫ ω, F n ω ∂μ)=
      (∫ ω, Real.log (empiricalMean X n ω) ∂μ)-(∫ ω, Y 0 ω ∂μ) := by
    rw [integral_sub (hilog n) (hiB n),integral_empiricalMean hiY (fun i ↦ (hidY i).integral_eq)]
  have hUpper (n) : (∫ ω, F n ω ∂μ)≤c := by
    rw [hIntegral]
    apply sub_le_sub_right
    have h := integral_log_le_log_integral (hiA n) (hilog n)
      (hpall.mono (fun ω hω ↦ empiricalMean_pos X n ω hω))
    rwa [integral_empiricalMean hiX (fun i ↦ (hid i).integral_eq)] at h
  have hFin : Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) atTop (𝓝 c) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' htrunc' tendsto_const_nhds
      (Eventually.of_forall (fun n ↦ integral_mono (hiC n) (hiF n) (fun ω ↦ min_le_left _ _)))
      (Eventually.of_forall hUpper)
  have hfinal := hFin.add_const (∫ ω, Y 0 ω ∂μ)
  simpa only [hIntegral,c,sub_add_cancel] using hfinal

end SKValueG

end

end OAI
