import Mathlib
import OAI.Analysis.FourierExtension.SurfaceBound
import OAI.Analysis.FourierExtension.AutomaticBound

namespace OAI

/-! Diagonal estimates above four and the remaining low-exponent condition. -/

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
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace DiagonalExtension
lemma memLp_above_four_of_bounded {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {g : α → E}
    (hg : MemLp g 4 μ) {M p : ℝ} (hb : ∀ᵐ x ∂μ, ‖g x‖ ≤ M) (hp : 4 ≤ p) :
    MemLp g (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have he : p = (p-4)+4 := by ring
  have ht : Integrable (fun x => ‖g x‖^(4 : ℕ)) μ := hg.integrable_norm_pow (by norm_num)
  have hdom : Integrable (fun x => (max 1 M)^(p-4) * ‖g x‖^(4 : ℕ)) μ := ht.const_mul _
  have hpow : Integrable (fun x => ‖g x‖^p) μ := by
    apply hdom.mono' (hg.aestronglyMeasurable.norm.aemeasurable.pow_const p).aestronglyMeasurable
    filter_upwards [hb] with x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      _ = ‖g x‖^(p-4) * ‖g x‖^(4 : ℕ) := by
        conv_lhs => rw [he]
        rw [Real.rpow_add_of_nonneg (norm_nonneg _) (by linarith) (by norm_num)]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (norm_nonneg _) (hx.trans (le_max_right 1 M)) (by linarith)) (by positivity)
  apply (integrable_norm_rpow_iff hg.aestronglyMeasurable
    (by simp [hp0] : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hp0.le] using hpow

theorem IsSurface.diagonal_extension_of_four_le {S : Set E3} (hS : IsSurface S)
    {p : ℝ} (hp : 4 ≤ p) :
    ∃ C : ℝ≥0, ∀ f : E3 → ℂ,
      MemLp f (ENNReal.ofReal p) (surfaceMeasure S) →
      MemLp (extension S f) (ENNReal.ofReal p) volume ∧
      eLpNorm (extension S f) (ENNReal.ofReal p) volume ≤
        (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) (surfaceMeasure S) := by
  have := hS.isFiniteMeasure
  let q := ENNReal.ofReal p
  have hq1 : (1 : ℝ≥0∞) ≤ q := by
    simpa only [q,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hq2 : (2 : ℝ≥0∞) ≤ q := by
    simpa only [q,ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal (show (2 : ℝ) ≤ p by linarith)
  have : Fact (1 ≤ q) := ⟨hq1⟩
  obtain ⟨C4,hC4⟩ := hS.extension_L4
  have hmem (f : E3 → ℂ) (hf : MemLp f q (surfaceMeasure S)) :
      MemLp (extension S f) q volume := by
    have hfi : Integrable f (surfaceMeasure S) := hf.integrable hq1
    exact memLp_above_four_of_bounded (hC4 f (hf.mono_exponent hq2)).1
      (Filter.Eventually.of_forall (norm_extension_le hfi)) hp
  have hk (x : E3) : AEStronglyMeasurable (fun ξ => fourierCharacter (inner ℝ x ξ))
      (surfaceMeasure S) :=
    (continuous_fourierCharacter.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
  have hkb (x : E3) : ∀ᵐ ξ ∂surfaceMeasure S, ‖fourierCharacter (inner ℝ x ξ)‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun _ => (norm_fourierCharacter _).le)
  let T : E3 → Lp ℂ q (surfaceMeasure S) →L[ℂ] ℂ :=
    fun x => KernelLp.eval ENNReal.ofReal_ne_top (hk x) (hkb x)
  have hT (v : Lp ℂ q (surfaceMeasure S)) : MemLp (fun x => T x v) q volume :=
    hmem (v : E3 → ℂ) (Lp.memLp v)
  obtain ⟨C,hC⟩ := AutomaticBound.exists_bound T hT
  refine ⟨C,fun f hf => ⟨hmem f hf,?_⟩⟩
  have he : (fun x => T x (hf.toLp f)) = extension S f := by
    funext x
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with ξ hξ
    rw [hξ]
  have hb := hC (hf.toLp f)
  rw [he,Lp.enorm_toLp] at hb
  exact hb



theorem mainStatement_iff_low_exponent_memLp :
    MainStatement ↔
      ∀ (S : Set E3), IsSurface S → ∀ p : ℝ, 3 < p → p < 4 →
        ∀ f : E3 → ℂ, MemLp f (ENNReal.ofReal p) (surfaceMeasure S) →
          MemLp (extension S f) (ENNReal.ofReal p) volume := by
  constructor
  · intro h S hS p hp _ f hf
    obtain ⟨C, hC⟩ := h S hS p hp
    exact (hC f hf).1
  · intro h S hS p hp
    by_cases hp4 : 4 ≤ p
    · exact hS.diagonal_extension_of_four_le hp4
    · have hmem := h S hS p hp (lt_of_not_ge hp4)
      have := hS.isFiniteMeasure
      let q := ENNReal.ofReal p
      have hq1 : (1 : ℝ≥0∞) ≤ q := by
        simpa only [q, ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
      have : Fact (1 ≤ q) := ⟨hq1⟩
      have hk (x : E3) : AEStronglyMeasurable
          (fun ξ => fourierCharacter (inner ℝ x ξ)) (surfaceMeasure S) :=
        (continuous_fourierCharacter.comp
          (continuous_const.inner continuous_id)).aestronglyMeasurable
      have hkb (x : E3) : ∀ᵐ ξ ∂surfaceMeasure S,
          ‖fourierCharacter (inner ℝ x ξ)‖ ≤ 1 :=
         Filter.Eventually.of_forall (fun _ => (norm_fourierCharacter _).le)
      let T : E3 → Lp ℂ q (surfaceMeasure S) →L[ℂ] ℂ :=
        fun x => KernelLp.eval ENNReal.ofReal_ne_top (hk x) (hkb x)
      have hT (v : Lp ℂ q (surfaceMeasure S)) :
          MemLp (fun x => T x v) q volume :=
        hmem (v : E3 → ℂ) (Lp.memLp v)
      obtain ⟨C, hC⟩ := AutomaticBound.exists_bound T hT
      refine ⟨C, fun f hf => ⟨hmem f hf, ?_⟩⟩
      have he : (fun x => T x (hf.toLp f)) = extension S f := by
        funext x
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with ξ hξ
        rw [hξ]
      have hb := hC (hf.toLp f)
      rw [he, Lp.enorm_toLp] at hb
      exact hb

end DiagonalExtension

end

end OAI
