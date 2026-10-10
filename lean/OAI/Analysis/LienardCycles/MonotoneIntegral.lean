import OAI.Analysis.LienardCycles.FitAngles

namespace OAI

universe uα

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter Metric
open Set Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace QuinticLienard.RealAnalysis

theorem ae_bddAbove_of_integral_bounded {α : Type uα} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {C : ℝ}
    (hf : ∀ n, Integrable (f n) μ)
    (hn : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f n x)
    (hm : ∀ᵐ x ∂μ, Monotone (fun n => f n x))
    (hI : ∀ n, (∫ x, f n x ∂μ) ≤ C) :
    ∀ᵐ x ∂μ, BddAbove (Set.range (fun n => f n x)) := by
  let F : ℕ → α → ℝ≥0∞ := fun n x => ENNReal.ofReal (f n x)
  have hFm : ∀ n, AEMeasurable (F n) μ := fun n => (hf n).aemeasurable.ennreal_ofReal
  have hFM : ∀ᵐ x ∂μ, Monotone (fun n => F n x) := by
    filter_upwards [hm] with x hx n m hnm
    exact ENNReal.ofReal_le_ofReal (hx hnm)
  have hfin : (∫⁻ x, ⨆ n, F n x ∂μ) < ⊤ := by
    rw [lintegral_iSup' hFm hFM]
    apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
    apply iSup_le
    intro n
    rw [←ofReal_integral_eq_lintegral_ofReal (hf n) (hn.mono (fun x hx => hx n))]
    exact ENNReal.ofReal_le_ofReal (hI n)
  filter_upwards [ae_lt_top' (AEMeasurable.iSup hFm) hfin.ne,hn] with x hx hxn
  refine ⟨(⨆ n, F n x).toReal,?_⟩
  rintro y ⟨n,rfl⟩
  have ht := ENNReal.toReal_mono hx.ne (le_iSup (fun n => F n x) n)
  simpa only [F,ENNReal.toReal_ofReal (hxn n)] using ht

lemma integral_pos_of_ae_pos {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    (hμ : μ Set.univ ≠ 0) {f : α → ℝ} (hf : Integrable f μ)
    (hp : ∀ᵐ x ∂μ, 0 < f x) : 0 < ∫ x, f x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae (hp.mono (fun _ h => h.le)) hf]
  have he : Function.support f =ᵐ[μ] Set.univ := by
    filter_upwards [hp] with x hx
    exact propext (iff_true_intro (ne_of_gt hx))
  rw [measure_congr he]
  exact pos_iff_ne_zero.mpr hμ
end QuinticLienard.RealAnalysis

end OAI
