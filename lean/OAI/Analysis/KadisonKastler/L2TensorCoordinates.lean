import OAI.Analysis.KadisonKastler.RegularCoreHilbertSum
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! # Scalar tensor coordinates for iterated L2 spaces

The scalar-vector tensor map preserves inner products and has dense range.
Swapping its two scalar factors therefore gives the L2 Fubini isometry
needed for the modular Fourier calculation.
-/

namespace KadisonKastler

open MeasureTheory
open scoped TensorProduct InnerProductSpace ENNReal

noncomputable section

variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def scalarLpTensor (μ : Measure X) : Lp ℂ 2 μ →L[ℂ] H →L[ℂ] Lp H 2 μ :=
  ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).flip.compLpL₂ 2 μ).flip

omit [CompleteSpace H] in
theorem scalarLpTensor_apply_ae (μ : Measure X) (f : Lp ℂ 2 μ) (x : H) :
    scalarLpTensor μ f x =ᵐ[μ] fun s => f s • x :=
  (ContinuousLinearMap.toSpanSingleton ℂ x).coeFn_compLp f

omit [CompleteSpace H] in
theorem inner_scalarLpTensor (μ : Measure X) (f g : Lp ℂ 2 μ) (x y : H) :
    inner ℂ (scalarLpTensor μ f x) (scalarLpTensor μ g y) =
      inner ℂ f g * inner ℂ x y := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ s, inner ℂ (f s) (g s) * inner ℂ x y ∂μ := by
      apply integral_congr_ae
      filter_upwards [scalarLpTensor_apply_ae μ f x, scalarLpTensor_apply_ae μ g y]
        with s hf hg
      rw [hf, hg]
      simp only [inner_smul_left, inner_smul_right, RCLike.inner_apply, mul_assoc]
    _ = _ := integral_mul_const _ _

def l2TensorLinearMap (μ : Measure X) : (Lp ℂ 2 μ ⊗[ℂ] H) →ₗ[ℂ] Lp H 2 μ :=
  TensorProduct.lift (scalarLpTensor (H := H) μ).toLinearMap₁₂

omit [CompleteSpace H] in
@[simp] theorem l2TensorLinearMap_tmul (μ : Measure X) (f : Lp ℂ 2 μ) (x : H) :
    l2TensorLinearMap μ (f ⊗ₜ[ℂ] x) = scalarLpTensor μ f x := rfl

omit [CompleteSpace H] in
theorem inner_l2TensorLinearMap (μ : Measure X) (z w : Lp ℂ 2 μ ⊗[ℂ] H) :
    inner ℂ (l2TensorLinearMap μ z) (l2TensorLinearMap μ w) = inner ℂ z w := by
  induction z using TensorProduct.inductionOn with
  | tmul f x =>
      induction w using TensorProduct.inductionOn with
      | tmul g y => exact inner_scalarLpTensor μ f g x y
      | add w₁ w₂ hw₁ hw₂ => simp only [map_add, inner_add_right, hw₁, hw₂]
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, inner_add_left, hz₁, hz₂]

def l2TensorEmbedding (μ : Measure X) : (Lp ℂ 2 μ ⊗[ℂ] H) →ₗᵢ[ℂ] Lp H 2 μ :=
  (l2TensorLinearMap μ).isometryOfInner (inner_l2TensorLinearMap μ)

omit [CompleteSpace H] in
theorem l2TensorEmbedding_dense (μ : Measure X) :
    DenseRange (l2TensorEmbedding (H := H) μ) := by
  let S := (l2TensorLinearMap (H := H) μ).range
  intro f
  change f ∈ S.topologicalClosure
  induction f using Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) with
  | @indicatorConst x s hs hfin =>
      apply Submodule.le_topologicalClosure
      refine ⟨(indicatorConstLp 2 hs hfin.ne (1 : ℂ)) ⊗ₜ[ℂ] x, ?_⟩
      change scalarLpTensor μ (indicatorConstLp 2 hs hfin.ne (1 : ℂ)) x =
        indicatorConstLp 2 hs hfin.ne x
      apply Lp.ext
      filter_upwards [scalarLpTensor_apply_ae μ (indicatorConstLp 2 hs hfin.ne (1 : ℂ)) x,
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin.ne) (c := (1 : ℂ)),
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin.ne) (c := x)] with t ht h1 hx
      rw [ht, h1, hx]
      by_cases hts : t ∈ s <;> simp [hts]
  | @add f g hf hg hdis hF hG => exact S.topologicalClosure.add_mem hF hG
  | isClosed => exact S.isClosed_topologicalClosure

def l2ScalarSwap (μ : Measure X) (ν : Measure Y) :
    Lp (Lp ℂ 2 ν) 2 μ ≃ₗᵢ[ℂ] Lp (Lp ℂ 2 μ) 2 ν :=
  (TensorProduct.comm ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)).extendOfIsometry
    (l2TensorEmbedding μ).toLinearMap (l2TensorEmbedding ν).toLinearMap
    (l2TensorEmbedding_dense μ) (l2TensorEmbedding_dense ν) (fun z => by
      change ‖l2TensorEmbedding ν (TensorProduct.comm ℂ _ _ z)‖ = ‖l2TensorEmbedding μ z‖
      rw [LinearIsometry.norm_map, LinearIsometry.norm_map, TensorProduct.norm_comm])

theorem l2ScalarSwap_tensor (μ : Measure X) (ν : Measure Y)
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    l2ScalarSwap μ ν (scalarLpTensor μ f g) = scalarLpTensor ν g f := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ (f ⊗ₜ[ℂ] g)

end

end KadisonKastler

end OAI
