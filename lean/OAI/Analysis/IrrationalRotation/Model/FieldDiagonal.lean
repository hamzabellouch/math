import OAI.Analysis.IrrationalRotation.Model.WeightedShift
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal lp Topology

namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem diagonal_value (w : Weight) (v : Hilbert) (i : ℤ) :
    diagonal w v i = w i * v i := rfl

theorem diagonal_bound (w : Weight) (C : ℝ) (hw : ‖w‖ ≤ C) (v : Hilbert) :
    ‖diagonal w v‖ ≤ C * ‖v‖ := by
  apply (diagonal w).le_of_opNorm_le
  exact (lp.norm_mapCLM_le 2 _ (norm_nonneg w) _).trans hw

theorem diagonal_aestronglyMeasurable (a : X → Weight) (C : ℝ) (_hC : 0 ≤ C)
    (_ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)
    {f : X → Hilbert} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => diagonal (a x) (f x)) μ := by
  classical
  let : Nonempty (Finset ℤ) := ⟨∅⟩
  let F : Finset ℤ → X → Hilbert :=
    fun s => ∑ i ∈ s, fun x => lp.single 2 i (a x i * f x i)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ℤ))
    (f := F)
  · intro s
    apply Finset.aestronglyMeasurable_sum
    intro i hi
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 i).continuous.comp_aestronglyMeasurable
      ((hm i).mul ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 i).continuous.comp_aestronglyMeasurable hf))
  · apply Filter.Eventually.of_forall
    intro x
    simpa only [F, Finset.sum_apply, diagonal_value, HasSum, SummationFilter.unconditional] using
      lp.hasSum_single (by norm_num) (diagonal (a x) (f x))

def fieldDiagonalVec (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)
    (f : Lp (Hilbert) 2 μ) : Lp (Hilbert) 2 μ :=
  ((Lp.memLp f).of_le_mul
    (diagonal_aestronglyMeasurable a C hC ha hm (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => diagonal_bound (a x) C (ha x) (f x))).toLp _

theorem fieldDiagonalVec_ae (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)
    (f : Lp (Hilbert) 2 μ) :
    fieldDiagonalVec a C hC ha hm f =ᵐ[μ]
      fun x => diagonal (a x) (f x) :=
  MemLp.coeFn_toLp _

def fieldDiagonalLinear (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ) :
    Lp (Hilbert) 2 μ →ₗ[ℂ] Lp (Hilbert) 2 μ where
  toFun := fieldDiagonalVec a C hC ha hm
  map_add' f g := by
    apply Lp.ext
    filter_upwards [fieldDiagonalVec_ae a C hC ha hm (f + g),
      fieldDiagonalVec_ae a C hC ha hm f, fieldDiagonalVec_ae a C hC ha hm g,
      Lp.coeFn_add f g, Lp.coeFn_add
        (fieldDiagonalVec a C hC ha hm f) (fieldDiagonalVec a C hC ha hm g)]
      with x hfg hf hg hsum hout
    simp only [Pi.add_apply] at hsum hout
    rw [hfg, hout, hf, hg, hsum, map_add]
  map_smul' c f := by
    change fieldDiagonalVec a C hC ha hm (c • f) = c • fieldDiagonalVec a C hC ha hm f
    apply Lp.ext
    filter_upwards [fieldDiagonalVec_ae a C hC ha hm (c • f),
      fieldDiagonalVec_ae a C hC ha hm f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (fieldDiagonalVec a C hC ha hm f)] with x hcf hf hsmul hout
    simp only [Pi.smul_apply] at hsmul hout
    rw [hcf, hout, hf, hsmul, map_smul]

def fieldDiagonal (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ) :
    Lp (Hilbert) 2 μ →L[ℂ] Lp (Hilbert) 2 μ :=
  (fieldDiagonalLinear a C hC ha hm).mkContinuous C (by
    intro f
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    change ∀ᵐ x ∂μ, ‖fieldDiagonalVec a C hC ha hm f x‖ ≤ C * ‖f x‖
    filter_upwards [fieldDiagonalVec_ae a C hC ha hm f] with x hx
    rw [hx]
    exact diagonal_bound (a x) C (ha x) (f x))

end Invariant233.WeightedShift

end

end OAI
