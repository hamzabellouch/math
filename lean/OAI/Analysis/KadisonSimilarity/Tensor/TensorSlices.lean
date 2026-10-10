import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-!
# Vanishing tensor slices in the propagation argument

A bounded weakly null family of vectors gives strongly vanishing slices of
any fixed vector in the completed Hilbert tensor product. This is the density
step in `lem:propagation`, with the uniform bound proved on the completion.
-/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Bessel's inequality makes every orthonormal sequence weakly null. -/
theorem orthonormal_inner_tendsto_zero (x : ℕ → E) (hx : Orthonormal ℂ x) (a : E) :
    Tendsto (fun n => inner ℂ (x n) a) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (hx.inner_products_summable (x := a)).tendsto_atTop_zero
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

/-- The Hilbert completion of the algebraic tensor product. -/
def HilbertTensor (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :=
  UniformSpace.Completion (E ⊗[ℂ] F)

/-- Keep the canonical completed-tensor structures named. In iterated word
spaces this shares the structure terms instead of expanding each completion
and algebraic tensor instance at every use. -/
instance hilbertTensorNormedAddCommGroup : NormedAddCommGroup (HilbertTensor E F) := by
  unfold HilbertTensor
  infer_instance

instance hilbertTensorInnerProductSpace : InnerProductSpace ℂ (HilbertTensor E F) := by
  unfold HilbertTensor
  infer_instance

instance hilbertTensorCompleteSpace : CompleteSpace (HilbertTensor E F) := by
  unfold HilbertTensor
  infer_instance

instance hilbertTensorCoe : Coe (E ⊗[ℂ] F) (HilbertTensor E F) :=
  ⟨fun x => (x : UniformSpace.Completion (E ⊗[ℂ] F))⟩

@[simp] theorem norm_hilbertTensor_coe (x : E ⊗[ℂ] F) :
    ‖(x : HilbertTensor E F)‖ = ‖x‖ :=
  UniformSpace.Completion.norm_coe x

/-- Contract the first tensor coordinate against `x`. -/
def algebraTensorSlice (x : E) : E ⊗[ℂ] F →L[ℂ] F :=
  (TensorProduct.lidIsometry ℂ F).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (TensorProduct.mapL (innerSL ℂ x) (ContinuousLinearMap.id ℂ F))

@[simp] theorem algebraTensorSlice_tmul (x a : E) (b : F) :
    algebraTensorSlice x (a ⊗ₜ[ℂ] b) = inner ℂ x a • b := by
  simp [algebraTensorSlice]

theorem norm_algebraTensorSlice_apply_le (x : E) (z : E ⊗[ℂ] F) :
    ‖algebraTensorSlice x z‖ ≤ ‖x‖ * ‖z‖ := by
  change ‖(TensorProduct.lidIsometry ℂ F)
    (TensorProduct.mapL (innerSL ℂ x) (ContinuousLinearMap.id ℂ F) z)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖TensorProduct.mapL (innerSL ℂ x) (ContinuousLinearMap.id ℂ F)‖ * ‖z‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖innerSL ℂ x‖ * ‖ContinuousLinearMap.id ℂ F‖) * ‖z‖ :=
      mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le _ _) (norm_nonneg _)
    _ ≤ ‖x‖ * ‖z‖ := by
      rw [innerSL_apply_norm]
      calc
        _ ≤ (‖x‖ * 1) * ‖z‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := F))
            (norm_nonneg x)) (norm_nonneg z)
        _ = _ := by ring

variable [CompleteSpace F]

/-- The slice extends uniquely to the completed Hilbert tensor product. -/
def tensorSlice (x : E) : HilbertTensor E F →L[ℂ] F :=
  (algebraTensorSlice x).fromCompletion

@[simp] theorem tensorSlice_coe (x : E) (z : E ⊗[ℂ] F) :
    tensorSlice x (z : HilbertTensor E F) = algebraTensorSlice x z :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

theorem norm_tensorSlice_apply_le (x : E) (z : HilbertTensor E F) :
    ‖tensorSlice x z‖ ≤ ‖x‖ * ‖z‖ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih z =>
    change ‖tensorSlice x (z : HilbertTensor E F)‖ ≤
      ‖x‖ * ‖(z : UniformSpace.Completion (E ⊗[ℂ] F))‖
    rw [tensorSlice_coe, UniformSpace.Completion.norm_coe]
    exact norm_algebraTensorSlice_apply_le x z

omit [CompleteSpace F] in
/-- First prove convergence on finite tensor sums, before taking completion. -/
theorem algebraTensorSlice_tendsto_zero (x : ℕ → E)
    (hweak : ∀ a : E, Tendsto (fun n => inner ℂ (x n) a) atTop (𝓝 0))
    (z : E ⊗[ℂ] F) :
    Tendsto (fun n => algebraTensorSlice (x n) z) atTop (𝓝 0) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simpa using (hweak a).smul_const b
  | add a b ha hb => simpa only [map_add, zero_add] using ha.add hb

/-- Weak convergence in the first factor yields norm convergence of each
fixed tensor slice. No uniform rate over tensor vectors is asserted. -/
theorem tensorSlice_tendsto_zero (x : ℕ → E)
    (hbound : ∀ n, ‖x n‖ ≤ 1)
    (hweak : ∀ a : E, Tendsto (fun n => inner ℂ (x n) a) atTop (𝓝 0))
    (z : HilbertTensor E F) :
    Tendsto (fun n => tensorSlice (x n) z) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨w, hw⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt z (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (algebraTensorSlice_tendsto_zero x hweak w)
    (ε / 2) (half_pos hε)
  let w' : HilbertTensor E F := w
  have hw' : dist z w' < ε / 2 := hw
  refine ⟨N, fun n hn => ?_⟩
  have happrox : ‖tensorSlice (x n) (z - w')‖ < ε / 2 := by
    calc
      _ ≤ ‖x n‖ * ‖z - w'‖ := norm_tensorSlice_apply_le _ _
      _ ≤ ‖z - w'‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (hbound n)
      _ < ε / 2 := by simpa only [dist_eq_norm] using hw'
  have hwN : ‖tensorSlice (x n) w'‖ < ε / 2 := by
    rw [show w' = (w : HilbertTensor E F) from rfl, tensorSlice_coe]
    simpa only [dist_zero_right] using hN n hn
  rw [dist_zero_right]
  calc
    _ ≤ ‖tensorSlice (x n) (z - w')‖ +
        ‖tensorSlice (x n) w'‖ := by
      simpa only [map_sub, sub_add_cancel] using
        norm_add_le (tensorSlice (x n) (z - w')) (tensorSlice (x n) w')
    _ < ε := by linarith

/-- In particular the normalized Haar powers used in propagation give
vanishing slices once their orthonormality has been established. -/
theorem tensorSlice_tendsto_zero_of_orthonormal (x : ℕ → E) (hx : Orthonormal ℂ x)
    (z : HilbertTensor E F) :
    Tendsto (fun n => tensorSlice (x n) z) atTop (𝓝 0) :=
  tensorSlice_tendsto_zero x (fun n => (hx.norm_eq_one n).le)
    (orthonormal_inner_tendsto_zero x hx) z

end KadisonSimilarity

end

end OAI
