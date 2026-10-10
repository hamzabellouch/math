import Mathlib

namespace OAI

/-! Automatic boundedness and integral kernels on Lp spaces. -/

open MeasureTheory
open scoped NNReal ENNReal ContDiff
noncomputable section
open Filter
open scoped Topology ContDiff
open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProductSpace ENNReal
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
open Set Filter
open scoped ENNReal InnerProductSpace
open scoped FourierTransform SchwartzMap ENNReal
open scoped ENNReal FourierTransform InnerProductSpace
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
open scoped ENNReal NNReal

open Filter
namespace DiagonalExtension.AutomaticBound
variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

def pointwiseLpMap (T : α → V →L[ℂ] ℂ)
    (hT : ∀ v, MemLp (fun x => T x v) p μ) : V →ₗ[ℂ] Lp ℂ p μ where
  toFun v := (hT v).toLp (fun x => T x v)
  map_add' v w := by
    apply Lp.ext
    filter_upwards [(hT (v+w)).coeFn_toLp,(hT v).coeFn_toLp,(hT w).coeFn_toLp,
      Lp.coeFn_add ((hT v).toLp _) ((hT w).toLp _)] with x h₁ h₂ h₃ h₄
    exact (h₁.trans ((T x).map_add v w)).trans (by rw [h₄,Pi.add_apply,h₂,h₃])
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [(hT (c • v)).coeFn_toLp,(hT v).coeFn_toLp,
      Lp.coeFn_smul c ((hT v).toLp _)] with x h₁ h₂ h₃
    exact (h₁.trans ((T x).map_smul c v)).trans (by rw [RingHom.id_apply,h₃,Pi.smul_apply,h₂])

theorem continuous_pointwiseLpMap (T : α → V →L[ℂ] ℂ)
    (hT : ∀ v, MemLp (fun x => T x v) p μ) :
    Continuous (pointwiseLpMap T hT) := by
  apply LinearMap.continuous_of_seq_closed_graph
  intro u v w hu hw
  obtain ⟨ns,hmono,hns⟩ := (tendstoInMeasure_of_tendsto_Lp hw).exists_seq_tendsto_ae
  apply Lp.ext
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
      pointwiseLpMap T hT (u (ns n)) x = T x (u (ns n)) := by
    exact ae_all_iff.mpr (fun n => (hT (u (ns n))).coeFn_toLp)
  filter_upwards [hns,hall,(hT v).coeFn_toLp] with x hx hxe hxv
  change w x = (hT v).toLp (fun x => T x v) x
  rw [hxv]
  have he : Tendsto (fun n => T x (u (ns n))) atTop (𝓝 (T x v)) :=
    ((T x).continuous.tendsto v).comp (hu.comp hmono.tendsto_atTop)
  have hw' : Tendsto (fun n => T x (u (ns n))) atTop (𝓝 (w x)) := by
    convert hx using 1
    ext n
    exact (hxe n).symm
  exact tendsto_nhds_unique hw' he

theorem exists_bound (T : α → V →L[ℂ] ℂ)
    (hT : ∀ v, MemLp (fun x => T x v) p μ) :
    ∃ C : ℝ≥0, ∀ v, eLpNorm (fun x => T x v) p μ ≤ (C : ℝ≥0∞) * ‖v‖ₑ := by
  let L : V →L[ℂ] Lp ℂ p μ :=
    ⟨pointwiseLpMap T hT, continuous_pointwiseLpMap T hT⟩
  refine ⟨‖L‖₊,fun v => ?_⟩
  have hb := L.le_opNorm v
  have he := ENNReal.ofReal_le_ofReal hb
  have hv : ‖L v‖ₑ = eLpNorm (fun x => T x v) p μ :=
    Lp.enorm_toLp (hT v)
  rw [← hv, ENNReal.coe_nnreal_eq]
  change ‖L v‖ₑ ≤ ENNReal.ofReal ‖L‖ * ‖v‖ₑ
  simpa only [ENNReal.ofReal_mul (norm_nonneg _),ofReal_norm] using he

end DiagonalExtension.AutomaticBound

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace DiagonalExtension.KernelLp
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma integral_norm_le_lp (hp : p ≠ (∞ : ℝ≥0∞)) (f : Lp ℂ p μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ (μ Set.univ ^ (1-1/p.toReal)).toReal * ‖f‖ := by
  have hpr : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (show (1:ℝ≥0∞) ≤ p from Fact.out)
  have hpow : 0 ≤ 1-1/p.toReal := by
    have ht : 0 < p.toReal := by linarith
    have hh : 1/p.toReal ≤ 1 := (div_le_one ht).mpr hpr
    linarith
  have hM : μ Set.univ ^ (1-1/p.toReal) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg hpow (measure_ne_top μ _)
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1:ℝ≥0∞) ≤ p from Fact.out) (Lp.aestronglyMeasurable f)
  simp only [ENNReal.toReal_one,div_one] at hh
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_ne_top hM) hh
  simpa only [ENNReal.toReal_mul,← Lp.norm_def,mul_comm] using hr

lemma integrable_kernel {k : α → ℂ} (hk : AEStronglyMeasurable k μ)
    (hb : ∀ᵐ x ∂μ, ‖k x‖ ≤ 1) (f : Lp ℂ p μ) :
    Integrable (fun x => f x * k x) μ :=
  ((Lp.memLp f).integrable (show (1:ℝ≥0∞) ≤ p from Fact.out)).mul_bdd hk hb

def evalLinear {k : α → ℂ} (hk : AEStronglyMeasurable k μ)
    (hb : ∀ᵐ x ∂μ, ‖k x‖ ≤ 1) : Lp ℂ p μ →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x * k x ∂μ
  map_add' f g := by
    calc
      _ = ∫ x, f x * k x + g x * k x ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with x hx
        rw [hx,Pi.add_apply,add_mul]
      _ = _ := integral_add (integrable_kernel hk hb f) (integrable_kernel hk hb g)
  map_smul' c f := by
    simp only [RingHom.id_apply]
    calc
      _ = ∫ x, c • (f x * k x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with x hx
        rw [hx,Pi.smul_apply,smul_mul_assoc]
      _ = _ := integral_smul _ _

lemma norm_evalLinear_le (hp : p ≠ (∞ : ℝ≥0∞)) {k : α → ℂ}
    (hk : AEStronglyMeasurable k μ) (hb : ∀ᵐ x ∂μ, ‖k x‖ ≤ 1)
    (f : Lp ℂ p μ) :
    ‖evalLinear hk hb f‖ ≤ (μ Set.univ ^ (1-1/p.toReal)).toReal * ‖f‖ := by
  have hi := ((Lp.memLp f).integrable (show (1:ℝ≥0∞) ≤ p from Fact.out)).norm
  apply le_trans (norm_integral_le_of_norm_le hi ?_) (integral_norm_le_lp hp f)
  filter_upwards [hb] with x hx
  exact (norm_mul _ _).le.trans (by simpa using mul_le_mul_of_nonneg_left hx (norm_nonneg (f x)))

def eval (hp : p ≠ (∞ : ℝ≥0∞)) {k : α → ℂ} (hk : AEStronglyMeasurable k μ)
    (hb : ∀ᵐ x ∂μ, ‖k x‖ ≤ 1) : Lp ℂ p μ →L[ℂ] ℂ :=
  (evalLinear hk hb).mkContinuous (μ Set.univ ^ (1-1/p.toReal)).toReal
    (norm_evalLinear_le hp hk hb)

@[simp] lemma eval_apply (hp : p ≠ (∞ : ℝ≥0∞)) {k : α → ℂ} (hk : AEStronglyMeasurable k μ)
    (hb : ∀ᵐ x ∂μ, ‖k x‖ ≤ 1) (f : Lp ℂ p μ) :
    eval hp hk hb f = ∫ x, f x * k x ∂μ := rfl

end DiagonalExtension.KernelLp

end

end OAI
