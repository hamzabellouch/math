import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRealShadow
import Mathlib.Algebra.Lie.Solvable

namespace OAI

/-! # The real shadow retains its nilpotent kernel and is solvable -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The same weight kernel, now inside the modified Lie algebra. -/
def realShadowKernel : LieIdeal ℝ (CartanRealShadow T H) where
  __ := (T.weightMap.comp (cartanRealShadowEquiv T H).symm.toLinearMap).ker
  lie_mem := by
    intro p q _
    change T.weightMap ((cartanRealShadowEquiv T H).symm ⁅p,q⁆) = 0
    obtain ⟨x,rfl⟩ := (cartanRealShadowEquiv T H).surjective p
    obtain ⟨y,rfl⟩ := (cartanRealShadowEquiv T H).surjective q
    exact cartanRealShadow_bracket_weight T H x y

/-- On the nilpotent ideal the modified and original brackets agree. -/
def realShadowKernelEquiv : T.kernelIdeal ≃ₗ⁅ℝ⁆ realShadowKernel T H where
  toFun x := ⟨cartanRealShadowEquiv T H x,by
    change T.weightMap ((cartanRealShadowEquiv T H).symm (cartanRealShadowEquiv T H x)) = 0
    simpa only [LinearEquiv.symm_apply_apply] using (T.mem_kernelIdeal (x : L)).mp x.property⟩
  invFun p := ⟨(cartanRealShadowEquiv T H).symm p.val,p.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (cartanRealShadowEquiv T H).symm_apply_apply x
  right_inv p := by
    apply Subtype.ext
    exact (cartanRealShadowEquiv T H).apply_symm_apply p.val
  map_add' x y := by
    apply Subtype.ext
    exact (cartanRealShadowEquiv T H).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact (cartanRealShadowEquiv T H).map_smul r x
  map_lie' {x y} := by
    apply Subtype.ext
    apply (cartanRealShadowEquiv T H).symm.injective
    change (cartanRealShadowEquiv T H).symm (cartanRealShadowEquiv T H ⁅(x : L),(y : L)⁆) =
      (cartanRealShadowEquiv T H).symm ⁅cartanRealShadowEquiv T H x,cartanRealShadowEquiv T H y⁆
    rw [LinearEquiv.symm_apply_apply,cartanRealShadow_bracket,
      T.weightImaginaryAction_kernel H x x.property,T.weightImaginaryAction_kernel H y y.property]
    simp

theorem realShadowKernel_nilpotent : LieRing.IsNilpotent (realShadowKernel T H) :=
  (realShadowKernelEquiv T H).nilpotent_iff_equiv_nilpotent.mp T.kernelIdeal_nilpotent

/-- The real shadow is solvable because its derived algebra lies in the
unchanged nilpotent weight kernel. -/
theorem cartanRealShadow_solvable : LieAlgebra.IsSolvable (CartanRealShadow T H) := by
  let K := realShadowKernel T H
  let : LieRing.IsNilpotent K := realShadowKernel_nilpotent T H
  have hder : derivedSeries ℝ (CartanRealShadow T H) 1 ≤ K := by
    intro z hz
    change z ∈ (derivedSeries ℝ (CartanRealShadow T H) 1 : Submodule ℝ (CartanRealShadow T H)) at hz
    rw [coe_derivedSeries_one_eq] at hz
    apply (Submodule.span_le.mpr ?_) hz
    rintro _ ⟨p,q,rfl⟩
    change T.weightMap ((cartanRealShadowEquiv T H).symm ⁅p,q⁆) = 0
    obtain ⟨x,rfl⟩ := (cartanRealShadowEquiv T H).surjective p
    obtain ⟨y,rfl⟩ := (cartanRealShadowEquiv T H).surjective q
    exact cartanRealShadow_bracket_weight T H x y
  obtain ⟨k,hk⟩ := IsSolvable.solvable ℝ K
  have hK : derivedSeriesOfIdeal ℝ (CartanRealShadow T H) k K = ⊥ :=
    (LieIdeal.derivedSeries_eq_bot_iff K k).mp hk
  apply IsSolvable.mk (R := ℝ) (k := k+1)
  apply le_antisymm _ bot_le
  change derivedSeriesOfIdeal ℝ (CartanRealShadow T H) (k+1) ⊤ ≤ ⊥
  rw [derivedSeriesOfIdeal_add]
  exact (derivedSeriesOfIdeal_mono hder k).trans (le_of_eq hK)

end PolycyclicRecognition

end

end OAI
