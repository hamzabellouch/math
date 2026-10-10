import Mathlib

namespace OAI

/-! Fourier integrals over finite measurable covers. -/

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

open MeasureTheory Set
open scoped ENNReal NNReal
namespace DiagonalExtension.MeasureFourier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def transform (μ : Measure E) (f : E → ℂ) (x : E) : ℂ :=
  ∫ y, f y * (Real.fourierChar (-inner ℝ y x) : ℂ) ∂μ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma char_continuous (x : E) :
    Continuous (fun y : E => (Real.fourierChar (-inner ℝ y x) : ℂ)) :=
  continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg)

omit [FiniteDimensional ℝ E] in
lemma integrand_integrable {μ : Measure E} {f : E → ℂ} (hf : Integrable f μ) (x : E) :
    Integrable (fun y => f y * (Real.fourierChar (-inner ℝ y x) : ℂ)) μ :=
  hf.mul_bdd (char_continuous x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => le_of_eq (Circle.norm_coe _)))

omit [FiniteDimensional ℝ E] in
lemma split {μ : Measure E} {f : E → ℂ} (hf : Integrable f μ)
    {V : Set E} (hV : MeasurableSet V) :
    transform μ f = transform (μ.restrict V) f + transform (μ.restrict Vᶜ) f := by
  ext x
  exact (integral_add_compl hV (integrand_integrable hf x)).symm

theorem finite_cover {ι : Type*} (t : Finset ι) (V : ι → Set E) (C : ι → ℝ≥0)
    (hV : ∀ i, MeasurableSet (V i)) {μ : Measure E} [IsFiniteMeasure μ]
    (hloc : ∀ i ∈ t, ∀ ν : Measure E, ν ≤ μ.restrict (V i) → ∀ f : E → ℂ,
      MemLp f 2 ν → MemLp (transform ν f) 4 volume ∧
        eLpNorm (transform ν f) 4 volume ≤ (C i : ℝ≥0∞) * eLpNorm f 2 ν) :
    ∀ ν : Measure E, ν ≤ μ → (∀ᵐ y ∂ν, ∃ i ∈ t, y ∈ V i) →
      ∀ f : E → ℂ, MemLp f 2 ν →
      MemLp (transform ν f) 4 volume ∧
        eLpNorm (transform ν f) 4 volume ≤
          ((∑ i ∈ t, C i) : ℝ≥0∞) * eLpNorm f 2 ν := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro ν hν hcover f hf
    have hν0 : ν = 0 := by
      have hh : ∀ᵐ y ∂ν, False := by simpa using hcover
      simpa using hh
    have hz : transform (0 : Measure E) f = 0 := by
      ext x; simp only [MeasureFourier.transform, integral_zero_measure, Pi.zero_apply]
    rw [hν0, hz]
    simp
  | @insert i t hi ih =>
    intro ν hν hcover f hf
    have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hν
    have hfr : MemLp f 2 (ν.restrict (V i)) := hf.mono_measure Measure.restrict_le_self
    have hfc : MemLp f 2 (ν.restrict (V i)ᶜ) := hf.mono_measure Measure.restrict_le_self
    obtain ⟨hm1,hb1⟩ := hloc i (Finset.mem_insert_self _ _) _
      (Measure.restrict_mono_measure hν (V i)) f hfr
    have hcover' : ∀ᵐ y ∂ν.restrict (V i)ᶜ, ∃ j ∈ t, y ∈ V j := by
      rw [ae_restrict_iff' (hV i).compl]
      filter_upwards [hcover] with y hy hnot
      obtain ⟨j,hj,hyj⟩ := hy
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hnot hyj).elim
      · exact ⟨j,hj,hyj⟩
    obtain ⟨hm2,hb2⟩ := ih (fun j hj => hloc j (Finset.mem_insert_of_mem hj))
      (ν.restrict (V i)ᶜ) (Measure.restrict_le_self.trans hν) hcover' f hfc
    rw [split (hf.integrable (by norm_num)) (hV i)]
    refine ⟨hm1.add hm2,?_⟩
    calc
      _ ≤ eLpNorm (transform (ν.restrict (V i)) f) 4 volume +
          eLpNorm (transform (ν.restrict (V i)ᶜ) f) 4 volume :=
        eLpNorm_add_le (by norm_num)
      _ ≤ (C i : ℝ≥0∞) * eLpNorm f 2 (ν.restrict (V i)) +
          ((∑ j ∈ t, C j) : ℝ≥0∞) * eLpNorm f 2 (ν.restrict (V i)ᶜ) := add_le_add hb1 hb2
      _ ≤ (C i : ℝ≥0∞) * eLpNorm f 2 ν + ((∑ j ∈ t, C j) : ℝ≥0∞) * eLpNorm f 2 ν := by
        exact add_le_add (mul_le_mul_right (eLpNorm_mono_measure f Measure.restrict_le_self) _)
          (mul_le_mul_right (eLpNorm_mono_measure f Measure.restrict_le_self) _)
      _ = _ := by rw [← add_mul, Finset.sum_insert hi]

end DiagonalExtension.MeasureFourier

end

end OAI
