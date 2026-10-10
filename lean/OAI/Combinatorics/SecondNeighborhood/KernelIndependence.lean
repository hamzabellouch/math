import OAI.Combinatorics.SecondNeighborhood.KernelConflict
import OAI.Combinatorics.SecondNeighborhood.MatrixMapsCommute
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Matrix
open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable section

theorem kernelB_vanishes_at_matched_left
    (r : X → X → Prop) (R C : Finset (X × X)) (b : X → X → ℝ)
    (hb : SupportedCoefficients r b) (hmax : LocalMaximalRanks r R C b)
    (left : ↥R) (right : ↥C) (hc : Conflict r left.val right.val)
    (v : ↥C → ℝ) (hv : (matrixN r R C b)ᵀ *ᵥ v = 0)
    (hcoordinate : v right = 1)
    (u : ↥R → ℝ) (hu : matrixB r R C b *ᵥ u = 0) : u left = 0 := by
  have h := conflict_kernel_product_eq_zero r R C b hb hmax
    u hu v hv left right hc
  simpa only [hcoordinate, mul_one] using h

theorem matrixB_lifts_linearIndependent
    {E : Type*} [Fintype E]
    (r : X → X → Prop) (R C : Finset (X × X)) (b : X → X → ℝ)
    (hb : SupportedCoefficients r b) (hmax : LocalMaximalRanks r R C b)
    (left : E → ↥R) (right : E → ↥C)
    (U : E → (↥R → ℝ)) (W : E → (↥C → ℝ))
    (hW : ∀ e, (matrixN r R C b)ᵀ *ᵥ W e = 0)
    (hWcoordinate : ∀ e, W e (right e) = 1)
    (hUcoordinate : ∀ e f, U e (left f) = if e = f then 1 else 0)
    (hconflict : ∀ e, Conflict r (left e).val (right e).val) :
    LinearIndependent ℝ (fun e => matrixB r R C b *ᵥ U e) := by
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients hrelation e
  let u : ↥R → ℝ := ∑ f, coefficients f • U f
  have hu : matrixB r R C b *ᵥ u = 0 := by
    change (matrixB r R C b).mulVecLin (∑ f, coefficients f • U f) = 0
    simpa only [map_sum, map_smul, Matrix.mulVecLin_apply] using hrelation
  have hzero : u (left e) = 0 :=
    kernelB_vanishes_at_matched_left r R C b hb hmax
      (left e) (right e) (hconflict e) (W e) (hW e) (hWcoordinate e) u hu
  have hcoordinate : u (left e) = coefficients e := by
    simp [u, Finset.sum_apply, Pi.smul_apply, hUcoordinate, smul_eq_mul, mul_ite]
  exact hcoordinate.symm.trans hzero

theorem matrixB_lift_mem_ker_matrixA
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (u : ↥R → ℝ) (hu : matrixL r R C a *ᵥ u = 0) :
    matrixB r R C b *ᵥ u ∈ LinearMap.ker (matrixA r R C a).mulVecLin := by
  rw [LinearMap.mem_ker]
  change matrixA r R C a *ᵥ (matrixB r R C b *ᵥ u) = 0
  rw [Matrix.mulVec_mulVec,
    ← matrixN_mul_matrixL_eq_matrixA_mul_matrixB r R C a b ha hb,
    ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]

theorem card_le_finrank_ker_matrixA_of_lifts
    {E : Type*} [Fintype E]
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (hmax : LocalMaximalRanks r R C b)
    (left : E → ↥R) (right : E → ↥C)
    (U : E → (↥R → ℝ)) (W : E → (↥C → ℝ))
    (hU : ∀ e, matrixL r R C a *ᵥ U e = 0)
    (hW : ∀ e, (matrixN r R C b)ᵀ *ᵥ W e = 0)
    (hWcoordinate : ∀ e, W e (right e) = 1)
    (hUcoordinate : ∀ e f, U e (left f) = if e = f then 1 else 0)
    (hconflict : ∀ e, Conflict r (left e).val (right e).val) :
    Fintype.card E ≤ Module.finrank ℝ (LinearMap.ker (matrixA r R C a).mulVecLin) := by
  let images : E → LinearMap.ker (matrixA r R C a).mulVecLin := fun e =>
    ⟨matrixB r R C b *ᵥ U e,
      matrixB_lift_mem_ker_matrixA r R C a b ha hb (U e) (hU e)⟩
  have hindependent : LinearIndependent ℝ images := by
    apply LinearIndependent.of_comp (LinearMap.ker (matrixA r R C a).mulVecLin).subtype
    change LinearIndependent ℝ (fun e => matrixB r R C b *ᵥ U e)
    exact matrixB_lifts_linearIndependent r R C b hb hmax left right U W
      hW hWcoordinate hUcoordinate hconflict
  exact hindependent.fintype_card_le_finrank

theorem card_add_rank_matrixN_mul_matrixL_le_card_H_of_lifts
    {E : Type*} [Fintype E]
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (hmax : LocalMaximalRanks r R C b)
    (left : E → ↥R) (right : E → ↥C)
    (U : E → (↥R → ℝ)) (W : E → (↥C → ℝ))
    (hU : ∀ e, matrixL r R C a *ᵥ U e = 0)
    (hW : ∀ e, (matrixN r R C b)ᵀ *ᵥ W e = 0)
    (hWcoordinate : ∀ e, W e (right e) = 1)
    (hUcoordinate : ∀ e f, U e (left f) = if e = f then 1 else 0)
    (hconflict : ∀ e, Conflict r (left e).val (right e).val) :
    Fintype.card E + (matrixN r R C b * matrixL r R C a).rank ≤ (H r R C).card := by
  have hcard := card_le_finrank_ker_matrixA_of_lifts r R C a b ha hb hmax
    left right U W hU hW hWcoordinate hUcoordinate hconflict
  have hnull : (matrixA r R C a).rank +
      Module.finrank ℝ (LinearMap.ker (matrixA r R C a).mulVecLin) = (H r R C).card := by
    simpa only [Matrix.rank, Module.finrank_pi, Fintype.card_coe] using
      LinearMap.finrank_range_add_finrank_ker (matrixA r R C a).mulVecLin
  rw [matrixN_mul_matrixL_eq_matrixA_mul_matrixB r R C a b ha hb]
  calc
    Fintype.card E + (matrixA r R C a * matrixB r R C b).rank ≤
        Module.finrank ℝ (LinearMap.ker (matrixA r R C a).mulVecLin) +
          (matrixA r R C a).rank :=
      Nat.add_le_add hcard (Matrix.rank_mul_le_left _ _)
    _ = (matrixA r R C a).rank +
        Module.finrank ℝ (LinearMap.ker (matrixA r R C a).mulVecLin) := Nat.add_comm _ _
    _ = (H r R C).card := hnull

end
end SeymourSecondNeighborhood.Pruning

end OAI
