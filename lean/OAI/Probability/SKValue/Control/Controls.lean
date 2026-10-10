import Mathlib

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def controlAccum {Ω : Type*} (γ : ℝ → ℝ)
    (α : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, γ s*(α (Real.toNNReal s) ω)^n

lemma progressive_clamped_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} (hα : IsProgressive f α) (t : ℝ≥0) :
    @Measurable (ℝ×Ω) ℝ (borel ℝ |>.prod (f t)) inferInstance
      (fun p ↦ α (min (Real.toNNReal p.1) t) p.2) := by
  have hj := hα t
  let : MeasurableSpace Ω := f t
  have hc : Measurable (fun p : ℝ×Ω ↦
      (⟨min (Real.toNNReal p.1) t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Iic t)) :=
    ((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk
  exact hj.comp (hc.prodMk measurable_snd)

lemma controlAccum_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ}
    (hα : IsProgressive f α) (hγ : Measurable γ) (n : ℕ) {t : ℝ} (ht : 0≤t) :
    Measurable[f (Real.toNNReal t)] (controlAccum γ α n t) := by
  let : MeasurableSpace Ω := f (Real.toNNReal t)
  have hm : Measurable (fun p : ℝ×Ω ↦ γ p.1*(α (min (Real.toNNReal p.1) (Real.toNNReal t)) p.2)^n) :=
    (hγ.comp measurable_fst).mul ((progressive_clamped_measurable (m := m) hα _).pow_const n)
  have heq : controlAccum γ α n t = fun ω ↦
      ∫ s in (0 : ℝ)..t, γ s*(α (min (Real.toNNReal s) (Real.toNNReal t)) ω)^n := by
    funext ω
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    dsimp only
    rw [min_eq_left (Real.toNNReal_mono hs.2)]
  rw [heq]
  unfold intervalIntegral
  exact hm.stronglyMeasurable.integral_prod_left.measurable.sub
    hm.stronglyMeasurable.integral_prod_left.measurable

lemma controlAccum_bound {Ω : Type*} {γ : ℝ → ℝ} {α : ℝ≥0 → Ω → ℝ}
    {T t G : ℝ} (ht : 0≤t) (htT : t≤T)
    (hα : ∀ s ω, |α s ω|≤1) (hγ : ∀ s∈Icc (0 : ℝ) T, |γ s|≤G)
    (n : ℕ) (ω : Ω) : |controlAccum γ α n t ω|≤t*G := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (f := fun s ↦ γ s*(α (Real.toNNReal s) ω)^n) (C := G) (fun s hs ↦ by
      rw [uIoc_of_le ht] at hs
      rw [Real.norm_eq_abs,abs_mul,abs_pow]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) (hα _ _)) (abs_nonneg _)).trans
        (by simpa only [mul_one] using hγ s ⟨hs.1.le,hs.2.trans htT⟩))
  simpa only [controlAccum,Real.norm_eq_abs,sub_zero,abs_of_nonneg ht,mul_comm G t] using hh

lemma controlAccum_integrable {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T t G : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hγb : ∀ s∈Icc (0 : ℝ) T, |γ s|≤G) (n : ℕ) (ht : 0≤t) (htT : t≤T) :
    Integrable (controlAccum γ α n t) μ := by
  apply Integrable.of_bound
    ((controlAccum_measurable hα hγ n ht).mono (f.le _) le_rfl).aestronglyMeasurable (t*G)
  exact Eventually.of_forall (fun ω ↦ by
    simpa only [Real.norm_eq_abs] using controlAccum_bound ht htT hαb hγb n ω)

lemma controlAccum_integrand_intervalIntegrable {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) (n : ℕ) (ω : Ω) :
    IntervalIntegrable (fun s ↦ γ s*(α (Real.toNNReal s) ω)^n) volume 0 T := by
  have hm : Measurable (fun s ↦ γ s*(α (min (Real.toNNReal s) (Real.toNNReal T)) ω)^n) := by
    let : MeasurableSpace Ω := f (Real.toNNReal T)
    exact hγ.mul (((progressive_clamped_measurable (m := m) hα _).comp
      (measurable_id.prodMk measurable_const)).pow_const n)
  have hint : IntervalIntegrable (fun s ↦ γ s*(α (min (Real.toNNReal s) (Real.toNNReal T)) ω)^n) volume 0 T := by
    apply hi.norm.mono_fun'
    · exact hm.aestronglyMeasurable
    · exact Eventually.of_forall (fun s ↦ by
        dsimp only
        rw [Real.norm_eq_abs,abs_mul,abs_pow,Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) (hαb _ _))
          (abs_nonneg _)).trans_eq (mul_one _))
  apply hint.congr
  intro s hs
  rw [uIoc_of_le hT] at hs
  dsimp only
  rw [min_eq_left (Real.toNNReal_mono hs.2)]

end SKValue

namespace SKValue

noncomputable def controlState {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (γ : ℝ → ℝ) (α : ℝ≥0 → Ω → ℝ) (x t : ℝ) (ω : Ω) : ℝ :=
  x+B (Real.toNNReal t) ω+controlAccum γ α 1 t ω

lemma controlState_past_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, StronglyMeasurable (B t))
    {γ : ℝ → ℝ} {α : ℝ≥0 → Ω → ℝ}
    (hα : IsProgressive (Filtration.natural B hBm) α) (hγ : Measurable γ) (x : ℝ)
    {t : ℝ} (ht : 0≤t) :
    StronglyMeasurable[Filtration.natural B hBm (Real.toNNReal t)] (controlState B γ α x t) :=
  (stronglyMeasurable_const.add (Filtration.stronglyAdapted_natural hBm _)).add
    (controlAccum_measurable hα hγ 1 ht).stronglyMeasurable

lemma controlState_memLp_two {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) (hBm : ∀ t, StronglyMeasurable (B t))
    {γ : ℝ → ℝ} {α : ℝ≥0 → Ω → ℝ} {T t G : ℝ}
    (hα : IsProgressive (Filtration.natural B hBm) α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hγb : ∀ s∈Icc (0 : ℝ) T, |γ s|≤G)
    (x : ℝ) (ht : 0≤t) (htT : t≤T) : MemLp (controlState B γ α x t) 2 μ := by
  have hi : MemLp (controlAccum γ α 1 t) 2 μ := MemLp.of_bound
    ((controlAccum_measurable hα hγ 1 ht).mono (Filtration.le _ _) le_rfl).aestronglyMeasurable
    (t*G) (Eventually.of_forall (fun ω ↦ by
      simpa only [Real.norm_eq_abs] using controlAccum_bound ht htT hαb hγb 1 ω))
  exact ((memLp_const x).add (hB.hasLaw_eval _).hasGaussianLaw.memLp_two).add hi

lemma controlState_initial {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (γ : ℝ → ℝ) (α : ℝ≥0 → Ω → ℝ) (x : ℝ) :
    ∀ᵐ ω ∂μ, controlState B γ α x 0 ω=x := by
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
  simp only [controlState,controlAccum,Real.toNNReal_zero,hω,add_zero,
    intervalIntegral.integral_same]

end SKValue

end

end OAI
