import Mathlib
import OAI.Probability.SKValue.GroundState.GumbelReplacement

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma rpow_le_add_one {x p : ℝ} (hx : 0≤x) (hp : 0≤p) (hp1 : p≤1) :
    x^p ≤ x+1 := by
  by_cases h : x≤1
  · have hh := Real.rpow_le_one hx h hp
    linarith
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hp1
    rw [Real.rpow_one] at hh
    linarith

lemma integrable_rpow_le_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hi : Integrable X μ)
    (hn : ∀ᵐ ω ∂μ, 0≤X ω) {p : ℝ} (hp : 0≤p) (hp1 : p≤1) :
    Integrable (fun ω ↦ (X ω)^p) μ := by
  apply (hi.abs.add (integrable_const 1)).mono'
    ((Real.continuous_rpow_const hp).comp_aestronglyMeasurable hi.aestronglyMeasurable)
  filter_upwards [hn] with ω hω
  simpa only [Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hω p),
    abs_of_nonneg hω] using rpow_le_add_one hω hp hp1

lemma integral_rpow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hi : Integrable X μ)
    (hn : ∀ᵐ ω ∂μ, 0≤X ω) {p : ℝ} (hp : 0≤p) (hp1 : p≤1) :
    (∫ ω, (X ω)^p ∂μ) ≤ (∫ ω, X ω ∂μ)^p :=
  (Real.concaveOn_rpow hp hp1).le_map_integral
    (Real.continuous_rpow_const hp).continuousOn isClosed_Ici hn hi
    (integrable_rpow_le_one hi hn hp hp1)

lemma nonneg_integrals_tendsto_of_upper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → Ω → ℝ} {c : ℝ}
    (hi : ∀ n, Integrable (F n) μ) (hn : ∀ n, ∀ᵐ ω ∂μ, 0≤F n ω)
    (hc : 0≤c) (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ F n ω) atTop (𝓝 c))
    (hup : ∀ n, (∫ ω, F n ω ∂μ)≤c) :
    Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) atTop (𝓝 c) := by
  have hiC (n) : Integrable (fun ω ↦ min (F n ω) c) μ := (hi n).inf (integrable_const c)
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ c)
    (fun n ↦ (hiC n).aestronglyMeasurable) (integrable_const c)
    (fun n ↦ (hn n).mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min hω hc)]
      exact min_le_right _ _))
    (hlim.mono (fun ω hω ↦ by simpa only [min_self] using hω.min (tendsto_const_nhds (x := c))))
  have ht' : Tendsto (fun n ↦ ∫ ω, min (F n ω) c ∂μ) atTop (𝓝 c) := by simpa using ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ht' tendsto_const_nhds
    (Eventually.of_forall (fun n ↦ integral_mono (hiC n) (hi n) (fun ω ↦ min_le_left _ _)))
    (Eventually.of_forall hup)

theorem expected_rpow_empiricalMean_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hi : Integrable (X 0) μ) (hp : ∀ i, ∀ᵐ ω ∂μ, 0≤X i ω)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1) :
    Tendsto (fun n ↦ ∫ ω, (empiricalMean X n ω)^p ∂μ)
      atTop (𝓝 ((∫ ω, X 0 ω ∂μ)^p)) := by
  have hiX (i) : Integrable (X i) μ := (hid i).integrable_iff.mpr hi
  have hiall (n) := empiricalMean_integrable hiX n
  have hpall := ae_all_iff.mpr hp
  have hpA (n) : ∀ᵐ ω ∂μ, 0≤empiricalMean X n ω := hpall.mono (fun ω hω ↦ by
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ ↦ hω i)
    · positivity)
  have hiA (n) := integrable_rpow_le_one (hiall n) (hpA n) hp0 hp1
  apply nonneg_integrals_tendsto_of_upper hiA
    (fun n ↦ (hpA n).mono (fun ω hω ↦ Real.rpow_nonneg hω p))
    (Real.rpow_nonneg (integral_nonneg_of_ae (hp 0)) p)
  · have hAX := strong_law_ae_real X hi hind hid
    exact hAX.mono (fun ω hω ↦ by
      have h := ((Real.continuous_rpow_const hp0).tendsto (∫ ω, X 0 ω ∂μ)).comp
        (hω.comp (tendsto_add_atTop_nat 1))
      simpa only [empiricalMean,Function.comp_def,Nat.cast_add,Nat.cast_one] using h)
  · intro n
    have h := integral_rpow_le (hiall n) (hpA n) hp0 hp1
    rwa [integral_empiricalMean hiX (fun i ↦ (hid i).integral_eq)] at h

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

noncomputable def gumbelExpMoment (p : ℝ) : ℝ := ∫ g,Real.exp (p*g) ∂gumbelLaw

lemma gumbelExpMoment_pos {p : ℝ} (hp : p<1) : 0<gumbelExpMoment p := by
  apply (integral_pos_iff_support_of_nonneg (fun g ↦ (Real.exp_pos (p*g)).le)
    (gumbel_exp_integrable hp)).mpr
  simp [Function.support,Real.exp_ne_zero]

lemma gumbelSmooth_exp (m a c : ℝ) :
    gumbelSmooth m (fun x ↦ Real.exp (a*x)) c=
      gumbelExpMoment (a/m)*Real.exp (a*c) := by
  have he (g : ℝ) : Real.exp (a*(g/m+c))=Real.exp ((a/m)*g)*Real.exp (a*c) := by
    rw [←Real.exp_add]; congr 1; ring
  simp only [gumbelSmooth,he,integral_mul_const,gumbelExpMoment]

lemma finite_centered_max_exp_moment {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) {m : ℝ} (hm : 0 < m) (a : ℝ) :
    (∫ z,Real.exp (a*(finiteMaximum (fun i ↦ d i+z i/m)-Real.log (Fintype.card ι : ℝ)/m))
      ∂Measure.pi (fun _ : ι ↦ gumbelLaw))=
    gumbelExpMoment (a/m)*((∑ i,Real.exp (m*d i))/(Fintype.card ι : ℝ))^(a/m) := by
  rw [scaled_gumbel_test_integral d hm (fun x ↦ Real.exp (a*x)) (by fun_prop),gumbelSmooth_exp]
  congr 1
  rw [Real.rpow_def_of_pos (div_pos (exp_sum_pos _) (by positivity))]
  congr 1
  ring

lemma empirical_branch_exp_identity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : ℕ → Ω → ℝ) {m : ℝ} (hm : 0 < m) (a : ℝ) (n : ℕ) :
    (∫ ω,(∫ z,Real.exp (a*(finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)-
        Real.log (n+1 : ℝ)/m)) ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw)) ∂μ)=
      gumbelExpMoment (a/m)*∫ ω,(empiricalMean (fun i ω ↦ Real.exp (m*X i ω)) n ω)^(a/m) ∂μ := by
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω ↦ by
    have h := finite_centered_max_exp_moment (fun i : Fin (n+1) ↦ X i ω) hm a
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ Real.exp (m*X i ω))] at h
    simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,empiricalMean] using h)

theorem marked_branching_exponential_limit {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    {m : ℝ} (hm : 0 < m) {a : ℝ} (ha : 0≤a) (ham : a < m)
    (he : Integrable (fun ω ↦ Real.exp (m*X 0 ω)) μ)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i,IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun n ↦ ∫ ω,(∫ z,Real.exp (a*(finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)-
        Real.log (n+1 : ℝ)/m)) ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw)) ∂μ)
      atTop (𝓝 (gumbelExpMoment (a/m)*(∫ ω,Real.exp (m*X 0 ω) ∂μ)^(a/m))) := by
  let Y := fun i ω ↦ Real.exp (m*X i ω)
  have hf : Measurable (fun x : ℝ ↦ Real.exp (m*x)) := by fun_prop
  have hp : 0≤a/m := div_nonneg ha hm.le
  have hp1 : a/m≤1 := (div_le_one hm).mpr ham.le
  have h := expected_rpow_empiricalMean_tendsto Y he
    (fun i ↦ Eventually.of_forall (fun ω ↦ (Real.exp_pos _).le))
    (fun i j hij ↦ (hind hij).comp hf hf) (fun i ↦ (hid i).comp hf) hp hp1
  simpa only [empirical_branch_exp_identity X hm a,Y] using h.const_mul (gumbelExpMoment (a/m))

theorem marked_branching_exponential_upper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    {m : ℝ} (hm : 0 < m) {a : ℝ} (ha : 0≤a) (ham : a < m)
    (he : Integrable (fun ω ↦ Real.exp (m*X 0 ω)) μ)
    (hid : ∀ i,IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    (∫ ω,(∫ z,Real.exp (a*(finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)-
        Real.log (n+1 : ℝ)/m)) ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw)) ∂μ)≤
      gumbelExpMoment (a/m)*(∫ ω,Real.exp (m*X 0 ω) ∂μ)^(a/m) := by
  rw [empirical_branch_exp_identity X hm a n]
  let Y := fun i ω ↦ Real.exp (m*X i ω)
  have hf : Measurable (fun x : ℝ ↦ Real.exp (m*x)) := by fun_prop
  have hiY (i) : Integrable (Y i) μ := ((hid i).comp hf).integrable_iff.mpr he
  have hpA : ∀ᵐ ω ∂μ,0≤empiricalMean Y n ω := Eventually.of_forall (fun ω ↦
    (empiricalMean_pos Y n ω (fun i ↦ Real.exp_pos _)).le)
  have h := integral_rpow_le (empiricalMean_integrable hiY n) hpA
    (div_nonneg ha hm.le) ((div_le_one hm).mpr ham.le)
  rw [integral_empiricalMean hiY (fun i ↦ ((hid i).comp hf).integral_eq)] at h
  exact mul_le_mul_of_nonneg_left h (gumbelExpMoment_pos ((div_lt_one hm).mpr ham)).le

end SKValueG

end

end OAI
