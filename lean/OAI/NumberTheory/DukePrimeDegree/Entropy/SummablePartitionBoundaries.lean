import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! # Choosing partition cuts with summable boundary returns

Almost every real cut of a measurable real-valued function has summable
strip masses for any summable sequence of widths. Invariant dynamics
therefore avoid those shrinking strips eventually almost everywhere.
This supplies the boundary control for partitions subordinate to
contracting root leaves.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

def realBoundaryStrip (f : Y → ℝ) (r ε : ℝ) : Set Y :=
  {x | |f x-r| ≤ ε}

lemma realBoundaryStrip_measurableSet {f : Y → ℝ} (hf : Measurable f) (r ε : ℝ) :
    MeasurableSet (realBoundaryStrip f r ε) := by
  simp only [realBoundaryStrip,abs_le]
  exact (measurableSet_le measurable_const (hf.sub_const r)).inter
    (measurableSet_le (hf.sub_const r) measurable_const)

lemma measurable_realBoundaryStrip_mass (μ : Measure Y) [SFinite μ]
    {f : Y → ℝ} (hf : Measurable f) (ε : ℝ) :
    Measurable (fun r => μ (realBoundaryStrip f r ε)) := by
  have hs : MeasurableSet {z : ℝ × Y | |f z.2-z.1| ≤ ε} := by
    simp only [abs_le]
    exact (measurableSet_le measurable_const ((hf.comp measurable_snd).sub measurable_fst)).inter
      (measurableSet_le ((hf.comp measurable_snd).sub measurable_fst) measurable_const)
  exact measurable_measure_prodMk_left hs

lemma lintegral_realBoundaryStrip_mass (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) (ε : ℝ) :
    (∫⁻ r : ℝ, μ (realBoundaryStrip f r ε)) = ENNReal.ofReal (2*ε) := by
  let S : Set (ℝ × Y) := {z | |f z.2-z.1| ≤ ε}
  have hS : MeasurableSet S := by
    simp only [S,abs_le]
    exact (measurableSet_le measurable_const ((hf.comp measurable_snd).sub measurable_fst)).inter
      (measurableSet_le ((hf.comp measurable_snd).sub measurable_fst) measurable_const)
  change (∫⁻ r : ℝ, μ (Prod.mk r ⁻¹' S)) = _
  rw [←Measure.prod_apply hS,Measure.prod_apply_symm hS]
  have hsection (x : Y) : (fun r : ℝ => (r,x)) ⁻¹' S = Icc (f x-ε) (f x+ε) := by
    ext r
    change |f x-r| ≤ ε ↔ f x-ε ≤ r ∧ r ≤ f x+ε
    rw [abs_le]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  simp_rw [hsection,Real.volume_Icc,show ∀ x : Y, f x+ε-(f x-ε)=2*ε by intro x; ring]
  simp only [lintegral_const,measure_univ,mul_one]

theorem ae_summable_realBoundaryStrip_mass (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) (ε : ℕ → ℝ) (hε : Summable ε) :
    ∀ᵐ r : ℝ, (∑' n, μ (realBoundaryStrip f r (ε n))) ≠ ∞ := by
  have hm (n : ℕ) := measurable_realBoundaryStrip_mass μ hf (ε n)
  have hI : (∫⁻ r : ℝ, ∑' n, μ (realBoundaryStrip f r (ε n))) ≠ ∞ := by
    rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
    simp_rw [lintegral_realBoundaryStrip_mass μ hf]
    exact (hε.mul_left 2).tsum_ofReal_ne_top
  exact (ae_lt_top (Measurable.tsum hm) hI).mono fun _ hr => hr.ne

lemma fiber_null_of_summable_realBoundaryStrip_mass
    (μ : Measure Y) {f : Y → ℝ} (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (r : ℝ)
    (hr : (∑' n, μ (realBoundaryStrip f r (ε n))) ≠ ∞) :
    μ {x | f x=r} = 0 := by
  by_contra h
  have hle : (∑' _ : ℕ, μ {x | f x=r}) ≤ ∑' n, μ (realBoundaryStrip f r (ε n)) := by
    apply ENNReal.tsum_le_tsum
    intro n
    apply measure_mono
    intro x hx
    change |f x-r| ≤ ε n
    rw [hx,sub_self,abs_zero]
    exact hε n
  rw [ENNReal.tsum_const_eq_top_of_ne_zero h] at hle
  exact hr (top_le_iff.mp hle)

theorem ae_eventually_avoid_realBoundaryStrip
    (μ : Measure Y) {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {f : Y → ℝ} (hf : Measurable f) (ε : ℕ → ℝ) (r : ℝ)
    (hr : (∑' n, μ (realBoundaryStrip f r (ε n))) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, ε n < |f (T^[n] x)-r| := by
  have hs (n : ℕ) : μ ((T^[n]) ⁻¹' realBoundaryStrip f r (ε n)) =
      μ (realBoundaryStrip f r (ε n)) :=
    (hT.iterate n).measure_preimage (realBoundaryStrip_measurableSet hf r (ε n)).nullMeasurableSet
  have H := ae_eventually_notMem (μ := μ)
    (s := fun n => (T^[n]) ⁻¹' realBoundaryStrip f r (ε n)) (by simpa only [hs] using hr)
  filter_upwards [H] with x hx
  exact hx.mono fun _ hn => lt_of_not_ge hn

theorem exists_cut_with_summable_boundary_returns
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {f : Y → ℝ} (hf : Measurable f) (ε : ℕ → ℝ)
    (hε : Summable ε) (hεpos : ∀ n, 0 ≤ ε n) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, μ {x | f x=r}=0 ∧
      ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, ε n < |f (T^[n] x)-r| := by
  obtain ⟨r,hr,hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioo a b) ≠ 0 by
      rw [Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne')
    (ae_restrict_of_ae (ae_summable_realBoundaryStrip_mass μ hf ε hε))
  exact ⟨r,hr,fiber_null_of_summable_realBoundaryStrip_mass μ ε hεpos r hgood,
    ae_eventually_avoid_realBoundaryStrip μ hT hf ε r hgood⟩

end DukePrimeDegree

end

end OAI
