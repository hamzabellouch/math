import Mathlib
import OAI.Probability.SKValue.GroundState.EmpiricalLog

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma finiteMaximum_div_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) {m : ℝ} (hm : 0 < m) :
    finiteMaximum (fun i ↦ d i/m)=finiteMaximum d/m := by
  apply le_antisymm
  · rw [finiteMaximum_le_iff]
    intro i
    exact div_le_div_of_nonneg_right (le_finiteMaximum d i) hm.le
  · obtain ⟨i,hi⟩ := exists_finiteMaximum d
    rw [←hi]
    exact le_finiteMaximum (fun i ↦ d i/m) i

lemma integral_scaled_gumbel_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) {m : ℝ} (hm : 0 < m) :
    (∫ z, finiteMaximum (fun i ↦ d i+z i/m) ∂Measure.pi (fun _ : ι ↦ gumbelLaw))=
      (gumbelMean+logSumExp (fun i ↦ m*d i))/m := by
  have he (z : ι → ℝ) : finiteMaximum (fun i ↦ d i+z i/m)=
      finiteMaximum (fun i ↦ m*d i+z i)/m := by
    rw [←finiteMaximum_div_pos _ hm]
    congr 1; ext i; field_simp
  simp_rw [he]
  rw [integral_div,integral_gumbel_max]

lemma centered_gumbel_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) {m : ℝ} (hm : 0 < m) :
    (∫ z, finiteMaximum (fun i ↦ d i+z i/m) ∂Measure.pi (fun _ : ι ↦ gumbelLaw))-
      (gumbelMean+Real.log (Fintype.card ι : ℝ))/m=
    Real.log ((∑ i, Real.exp (m*d i))/(Fintype.card ι : ℝ))/m := by
  rw [integral_scaled_gumbel_max d hm,Real.log_div (exp_sum_pos _).ne' (by positivity)]
  dsimp [logSumExp]
  ring

theorem finite_branching_logheat_limit {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    {m : ℝ} (hm : 0 < m) (hi : Integrable (X 0) μ)
    (he : Integrable (fun ω ↦ Real.exp (m*X 0 ω)) μ)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun n ↦ ∫ ω,
      ((∫ z, finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)
          ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw))-
        (gumbelMean+Real.log (n+1 : ℝ))/m) ∂μ)
      atTop (𝓝 (Real.log (∫ ω, Real.exp (m*X 0 ω) ∂μ)/m)) := by
  let Y := fun i ω ↦ Real.exp (m*X i ω)
  have hf : Measurable (fun x : ℝ ↦ Real.exp (m*x)) := by fun_prop
  have hlog : Integrable (fun ω ↦ Real.log (Y 0 ω)) μ := by
    simpa only [Y,Real.log_exp] using hi.const_mul m
  have h := expected_log_empiricalMean_tendsto Y he hlog
    (fun i ↦ Eventually.of_forall (fun ω ↦ Real.exp_pos _))
    (fun i j hij ↦ (hind hij).comp hf hf) (fun i ↦ (hid i).comp hf)
  have H := h.div_const m
  have heq (n : ℕ) :
      (∫ ω, ((∫ z, finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)
          ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw))-
        (gumbelMean+Real.log (n+1 : ℝ))/m) ∂μ)=
      (∫ ω, Real.log (empiricalMean Y n ω) ∂μ)/m := by
    rw [←integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω ↦ by
      have hh := centered_gumbel_max (fun i : Fin (n+1) ↦ X i ω) hm
      rw [Fin.sum_univ_eq_sum_range (fun i ↦ Real.exp (m*X i ω))] at hh
      simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,empiricalMean,Y] using hh)
  simpa only [heq,Y] using H

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma iid_empiricalMean_L1 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hi : Integrable (X 0) μ)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun n ↦ ∫ ω, |empiricalMean X n ω-(∫ ω, X 0 ω ∂μ)| ∂μ)
      atTop (𝓝 0) := by
  have hh := strong_law_Lp (p := 1) le_rfl (by simp) X (memLp_one_iff_integrable.mpr hi) hind hid
  have h := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞)≠⊤)).tendsto.comp
    (hh.comp (tendsto_add_atTop_nat 1))
  have hiX (i) : Integrable (X i) μ := (hid i).integrable_iff.mpr hi
  have he (n : ℕ) :
      (∫ ω, |empiricalMean X n ω-(∫ ω, X 0 ω ∂μ)| ∂μ)=
      (eLpNorm (fun ω ↦ (n+1 : ℝ)⁻¹ • (∑ i ∈ Finset.range (n+1),X i ω)-
        (∫ ω, X 0 ω ∂μ)) 1 μ).toReal := by
    have hm := ((empiricalMean_integrable hiX n).sub (integrable_const (∫ ω,X 0 ω ∂μ))).aestronglyMeasurable
    change AEStronglyMeasurable (fun ω ↦ empiricalMean X n ω-(∫ ω,X 0 ω ∂μ)) μ at hm
    rw [eLpNorm_one_eq_lintegral_enorm (by
      simpa only [empiricalMean,smul_eq_mul,div_eq_mul_inv,mul_comm,Pi.sub_apply] using hm)]
    simpa only [empiricalMean,smul_eq_mul,div_eq_mul_inv,mul_comm,Pi.sub_apply,Real.norm_eq_abs]
      using integral_norm_eq_lintegral_enorm hm
  simpa only [he,Function.comp_def,Nat.cast_add,Nat.cast_one,ENNReal.toReal_zero] using h

lemma nonnegative_L1_of_ae_and_integrals {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → Ω → ℝ} {c : ℝ}
    (hi : ∀ n, Integrable (F n) μ) (hn : ∀ n, ∀ᵐ ω ∂μ, 0≤F n ω)
    (hc : 0≤c) (hlim : ∀ᵐ ω ∂μ,Tendsto (fun n ↦ F n ω) atTop (𝓝 c))
    (hI : Tendsto (fun n ↦ ∫ ω,F n ω ∂μ) atTop (𝓝 c)) :
    Tendsto (fun n ↦ ∫ ω,|F n ω-c| ∂μ) atTop (𝓝 0) := by
  have hiC (n) : Integrable (fun ω ↦ min (F n ω) c) μ := (hi n).inf (integrable_const c)
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ c)
    (fun n ↦ (hiC n).aestronglyMeasurable) (integrable_const c)
    (fun n ↦ (hn n).mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min hω hc)]
      exact min_le_right _ _))
    (hlim.mono (fun ω hω ↦ by simpa only [min_self] using hω.min (tendsto_const_nhds (x := c))))
  have ht' : Tendsto (fun n ↦ ∫ ω,min (F n ω) c ∂μ) atTop (𝓝 c) := by simpa using ht
  have he (n) : (∫ ω,|F n ω-c| ∂μ)=(∫ ω,F n ω ∂μ)+c-2*(∫ ω,min (F n ω) c ∂μ) := by
    have eq (ω) : |F n ω-c|=F n ω+c-2*min (F n ω) c := by
      rcases le_total (F n ω) c with h|h
      · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
    simp_rw [eq]
    rw [integral_sub (f := fun ω ↦ F n ω+c) (g := fun ω ↦ 2*min (F n ω) c)
      ((hi n).add (integrable_const c)) ((hiC n).const_mul 2),
      integral_add (f := F n) (g := fun _ ↦ c) (hi n) (integrable_const c),integral_const_mul,integral_const]
    simp
  have h := (hI.add_const c).sub (ht'.const_mul 2)
  simpa only [he,show c+c-2*c=0 by ring] using h

lemma empiricalMean_log_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiX : ∀ i,Integrable (X i) μ)
    (hiY : ∀ i,Integrable (fun ω ↦ Real.log (X i ω)) μ)
    (hp : ∀ i,∀ᵐ ω ∂μ,0<X i ω) (n : ℕ) :
    Integrable (fun ω ↦ Real.log (empiricalMean X n ω)) μ := by
  let Y := fun i ω ↦ Real.log (X i ω)
  have hiA := empiricalMean_integrable hiX n
  have hiB := empiricalMean_integrable hiY n
  apply ((hiA.sub (integrable_const 1)).abs.add hiB.abs).mono'
    ((Real.measurable_log.comp_aemeasurable hiA.aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
  filter_upwards [ae_all_iff.mpr hp] with ω hω
  have hpA := empiricalMean_pos X n ω hω
  have hlo := empirical_log_lower X n ω hω
  have hup := log_tangent_bound hpA (show (0 : ℝ)<1 by norm_num)
  simp only [div_one,Real.log_one,add_zero] at hup
  change |Real.log (empiricalMean X n ω)|≤|empiricalMean X n ω-1|+|empiricalMean Y n ω|
  apply abs_le.mpr
  constructor
  · have hh := neg_abs_le (empiricalMean Y n ω)
    have hh' := abs_nonneg (empiricalMean X n ω-1)
    change empiricalMean Y n ω≤_ at hlo
    linarith
  · have hh := le_abs_self (empiricalMean X n ω-1)
    have hh' := abs_nonneg (empiricalMean Y n ω)
    linarith

theorem log_empiricalMean_L1 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hi : Integrable (X 0) μ) (hl : Integrable (fun ω ↦ Real.log (X 0 ω)) μ)
    (hp : ∀ i,∀ᵐ ω ∂μ,0<X i ω)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i,IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun n ↦ ∫ ω,|Real.log (empiricalMean X n ω)-Real.log (∫ ω,X 0 ω ∂μ)| ∂μ)
      atTop (𝓝 0) := by
  let Y := fun i ω ↦ Real.log (X i ω)
  have hiX (i) : Integrable (X i) μ := (hid i).integrable_iff.mpr hi
  have hidY (i) : IdentDistrib (Y i) (Y 0) μ μ := (hid i).comp Real.measurable_log
  have hiY (i) : Integrable (Y i) μ := (hidY i).integrable_iff.mpr hl
  have hindY : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) Y) :=
    fun i j hij ↦ (hind hij).comp Real.measurable_log Real.measurable_log
  have hpos : 0<∫ ω,X 0 ω ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae ((hp 0).mono (fun _ h ↦ h.le)) hi).mpr (by
      have hs : Function.support (X 0)=ᵐ[μ] univ := (hp 0).mono (fun ω hω ↦ by
        apply propext; change X 0 ω≠0 ↔ True; simp [hω.ne'])
      rw [measure_congr hs]; simp)
  have hilog (n) := empiricalMean_log_integrable X hiX hiY hp n
  have hiB (n) := empiricalMean_integrable hiY n
  let c := Real.log (∫ ω,X 0 ω ∂μ)-(∫ ω,Y 0 ω ∂μ)
  let F := fun n ω ↦ Real.log (empiricalMean X n ω)-empiricalMean Y n ω
  have hiF (n) : Integrable (F n) μ := (hilog n).sub (hiB n)
  have hFpos (n) : ∀ᵐ ω ∂μ,0≤F n ω := (ae_all_iff.mpr hp).mono (fun ω hω ↦
    sub_nonneg.mpr (empirical_log_lower X n ω hω))
  have hc : 0≤c := sub_nonneg.mpr (integral_log_le_log_integral hi hl (hp 0))
  have hlima : ∀ᵐ ω ∂μ,Tendsto (fun n ↦ F n ω) atTop (𝓝 c) := by
    filter_upwards [strong_law_ae_real X hi hind hid,strong_law_ae_real Y hl hindY hidY] with ω hX hY
    have hx := (hX.comp (tendsto_add_atTop_nat 1)).log hpos.ne'
    have hy := hY.comp (tendsto_add_atTop_nat 1)
    simpa only [F,c,empiricalMean,Function.comp_def,Nat.cast_add,Nat.cast_one] using hx.sub hy
  have hlimI : Tendsto (fun n ↦ ∫ ω,F n ω ∂μ) atTop (𝓝 c) := by
    have h := (expected_log_empiricalMean_tendsto X hi hl hp hind hid).sub_const (∫ ω,Y 0 ω ∂μ)
    have he (n) : (∫ ω,F n ω ∂μ)=(∫ ω,Real.log (empiricalMean X n ω) ∂μ)-(∫ ω,Y 0 ω ∂μ) := by
      rw [integral_sub (hilog n) (hiB n),integral_empiricalMean hiY (fun i ↦ (hidY i).integral_eq)]
    simpa only [he,c] using h
  have hF := nonnegative_L1_of_ae_and_integrals hiF hFpos hc hlima hlimI
  have hY := iid_empiricalMean_L1 Y hl hindY hidY
  have hlim : Tendsto (fun n ↦ (∫ ω,|F n ω-c| ∂μ)+
      (∫ ω,|empiricalMean Y n ω-(∫ ω,Y 0 ω ∂μ)| ∂μ)) atTop (𝓝 0) := by simpa using hF.add hY
  apply squeeze_zero (fun n ↦ integral_nonneg (fun ω ↦ abs_nonneg _)) _ hlim
  intro n
  rw [←integral_add (f := fun ω ↦ |F n ω-c|)
    (g := fun ω ↦ |empiricalMean Y n ω-(∫ ω,Y 0 ω ∂μ)|)
    ((hiF n).sub (integrable_const c)).abs
    ((hiB n).sub (integrable_const _)).abs]
  apply integral_mono ((hilog n).sub (integrable_const _)).abs
    (((hiF n).sub (integrable_const c)).abs.add ((hiB n).sub (integrable_const _)).abs)
  intro ω
  have he : Real.log (empiricalMean X n ω)-Real.log (∫ ω,X 0 ω ∂μ)=
      (F n ω-c)+(empiricalMean Y n ω-(∫ ω,Y 0 ω ∂μ)) := by dsimp [F,c]; ring
  change |Real.log (empiricalMean X n ω)-Real.log (∫ ω,X 0 ω ∂μ)| ≤
    |F n ω-c|+|empiricalMean Y n ω-(∫ ω,Y 0 ω ∂μ)|
  rw [he]
  exact abs_add_le _ _

end SKValueG

end

end OAI
