import OAI.Analysis.FiniteFactor.CrossedProduct.Cocycle
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The regular representation written as L2(X × Z), canonically equivalent
to the source's L2(X; l2(Z)). -/
abbrev sourceMeasure (ι : Type*) : Measure ((ι → ℝ) × ℤ) :=
  (Measure.infinitePi (fun _ : ι => unitIntervalMeasure)).prod Measure.count

abbrev SourceHilbert (ι : Type*) : Type _ := Lp ℂ 2 (sourceMeasure ι)

/-- The actual diagonal entry f(sigma^k x) of pi(f). -/
def sourceDiagonal {ι : Type*} (θ c : ι → ℝ) (z : (ι → ℝ) × ℤ) : ℂ :=
  sourceCocycle θ c 1 (coordinateRotate θ z.2 z.1)

theorem sourceDiagonal_measurable {ι : Type*} [Countable ι] (θ c : ι → ℝ) :
    Measurable (sourceDiagonal θ c) := by
  apply Complex.measurable_ofReal.comp
  apply (sourceCocycle_measurable θ c 1).comp
  apply Measurable.of_eval
  intro i
  unfold coordinateRotate
  fun_prop

theorem sourceDiagonal_norm_le {ι : Type*} (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (z : (ι → ℝ) × ℤ) :
    ‖sourceDiagonal θ c z‖ ≤ 1 := by
  rw [sourceDiagonal, Complex.norm_real, Real.norm_of_nonneg (sourceCocycle_pos _ _ _ _).le]
  apply sourceWeight_le_one θ c hθ hc
  intro i
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem sourceDiagonal_ne_zero {ι : Type*} (θ c : ι → ℝ) (z : (ι → ℝ) × ℤ) :
    sourceDiagonal θ c z ≠ 0 := by
  unfold sourceDiagonal
  exact_mod_cast (sourceCocycle_pos θ c 1 (coordinateRotate θ z.2 z.1)).ne'

theorem sourceDiagonal_memLp {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) :
    MemLp (sourceDiagonal θ c) ∞ (sourceMeasure ι) :=
  memLp_top_of_bound (sourceDiagonal_measurable θ c).aestronglyMeasurable 1
    (Eventually.of_forall (sourceDiagonal_norm_le θ c hθ hc))

/-- A bounded multiplication operator from the actual source formula. -/
def sourceMultiplication {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) : SourceHilbert ι →L[ℂ] SourceHilbert ι :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (sourceMeasure ι) ∞ 2 2
    ((sourceDiagonal_memLp θ c hθ hc).toLp (sourceDiagonal θ c))

theorem sourceMultiplication_apply_ae {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (f : SourceHilbert ι) :
    sourceMultiplication θ c hθ hc f =ᵐ[sourceMeasure ι] fun z => sourceDiagonal θ c z * f z := by
  have hh := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((sourceDiagonal_memLp θ c hθ hc).toLp (sourceDiagonal θ c)) f (r := 2)
  filter_upwards [hh, (sourceDiagonal_memLp θ c hθ hc).coeFn_toLp] with z hz hw
  simpa [sourceMultiplication, hw] using hz

theorem sourceMultiplication_injective {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) :
    Function.Injective (sourceMultiplication θ c hθ hc) := by
  intro f g hfg
  apply Lp.ext
  filter_upwards [sourceMultiplication_apply_ae θ c hθ hc f,
    sourceMultiplication_apply_ae θ c hθ hc g] with z hf hg
  rw [hfg, hg] at hf
  exact mul_left_cancel₀ (sourceDiagonal_ne_zero θ c z) hf.symm

/-- The shift S e_k=e_(k+1), so its action on coordinate functions uses k-1. -/
def sourceShiftIndex {ι : Type*} (z : (ι → ℝ) × ℤ) : (ι → ℝ) × ℤ := (z.1, z.2-1)

theorem sourceShiftIndex_preserving (ι : Type*) :
    MeasurePreserving (sourceShiftIndex (ι := ι)) (sourceMeasure ι) (sourceMeasure ι) := by
  have hm : Measurable (fun k : ℤ => k-1) := measurable_of_countable _
  have hi : Function.Injective (fun k : ℤ => k-1) := by intro a b h; dsimp at h; omega
  have hs : Function.Surjective (fun k : ℤ => k-1) := by intro k; exact ⟨k+1, by dsimp; omega⟩
  have hp : MeasurePreserving (fun k : ℤ => k-1) Measure.count Measure.count := by
    refine ⟨hm, ?_⟩
    ext S hS
    rw [Measure.map_apply hm hS, Measure.count_apply (hS.preimage hm), Measure.count_apply hS,
      ← hi.encard_image, Set.image_preimage_eq S hs]
  exact (MeasurePreserving.id _).prod hp

def sourceShift (ι : Type*) : SourceHilbert ι →L[ℂ] SourceHilbert ι :=
  (Lp.compMeasurePreservingₗᵢ ℂ sourceShiftIndex (sourceShiftIndex_preserving ι)).toContinuousLinearMap

/-- T=U pi(f), constructed as a bounded operator, with no assumed factor or
invariant-subspace properties. -/
def sourceOperator {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) : SourceHilbert ι →L[ℂ] SourceHilbert ι :=
  (sourceShift ι).comp (sourceMultiplication θ c hθ hc)

theorem sourceOperator_injective {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) :
    Function.Injective (sourceOperator θ c hθ hc) := by
  intro f g h
  apply sourceMultiplication_injective θ c hθ hc
  exact (Lp.compMeasurePreservingₗᵢ ℂ sourceShiftIndex
    (sourceShiftIndex_preserving ι)).injective h

theorem sourceMultiplication_norm_le {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (f : SourceHilbert ι) :
    ‖sourceMultiplication θ c hθ hc f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sourceMultiplication_apply_ae θ c hθ hc f] with z hz
  rw [hz, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (sourceDiagonal_norm_le θ c hθ hc z)

theorem sourceOperator_norm_le_one {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) : ‖sourceOperator θ c hθ hc‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖Lp.compMeasurePreserving sourceShiftIndex (sourceShiftIndex_preserving ι)
    (sourceMultiplication θ c hθ hc f)‖ ≤ 1 * ‖f‖
  rw [Lp.norm_compMeasurePreserving, one_mul]
  exact sourceMultiplication_norm_le θ c hθ hc f

/-- This constructs a nonzero bounded T, independently of any candidate projection. -/
theorem sourceOperator_ne_zero {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) : sourceOperator θ c hθ hc ≠ 0 := by
  let A : Set ((ι → ℝ) × ℤ) := Set.univ ×ˢ {0}
  have hA : MeasurableSet A := MeasurableSet.univ.prod (measurableSet_singleton 0)
  have hmass : sourceMeasure ι A = 1 := by simp [A, sourceMeasure, Measure.prod_prod]
  let e : SourceHilbert ι := indicatorConstLp 2 hA (by rw [hmass]; exact ENNReal.one_ne_top) 1
  have hen : ‖e‖ = 1 := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp [measureReal_def, hmass]
  have he : e ≠ 0 := by intro he; rw [he, norm_zero] at hen; norm_num at hen
  intro hT
  apply he
  apply sourceOperator_injective θ c hθ hc
  simp [hT]

end
end FiniteFactor

end OAI
