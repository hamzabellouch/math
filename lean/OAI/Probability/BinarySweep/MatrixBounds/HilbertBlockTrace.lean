import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.LinearEvenMoment
import OAI.Probability.BinarySweep.YoungTheory.HookInducedMoment
import OAI.Probability.BinarySweep.MatrixBounds.BlockTrace

namespace OAI


noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open TraceHolder

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
local notation "HW" => CoindHilbertSpace (I:=I) (W:=W)

omit [DecidableEq I] [FiniteDimensional ℂ W] in
lemma fiber_sum (v : HW) : ∑i, fiberInclude i (v i)=v := by
  classical
  apply (WithLp.linearEquiv 2 ℂ (I → W)).injective
  simp only [map_sum]
  ext i
  simp only [fiberInclude,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,LinearMap.single_apply,Finset.sum_apply,Pi.single_apply]
  simp only [WithLp.coe_linearEquiv]
  let : DecidableEq I := fun i j => Classical.propDecidable (i=j)
  exact (Finset.sum_ite_eq Finset.univ i (fun x => v x)).trans (ite_eq_left (Finset.mem_univ i))

omit [DecidableEq I] [FiniteDimensional ℂ W] in
lemma fiber_identity : (∑i : I, (fiberInclude i).comp (fiberProject i))=(1 : HW →ₗ[ℂ] HW) := by
  apply LinearMap.ext
  intro v
  simpa only [LinearMap.sum_apply,LinearMap.comp_apply, fiberProject, Module.End.one_apply,
    LinearEquiv.coe_coe, LinearMap.proj_apply, WithLp.coe_linearEquiv] using fiber_sum v

omit [DecidableEq I] [FiniteDimensional ℂ W] in
lemma hilbertBlock_mul (A B : HW →ₗ[ℂ] HW) (i j : I) :
    hilbertBlock (A*B) i j = ∑a, hilbertBlock A i a * hilbertBlock B a j := by
  ext v
  change A (B (fiberInclude j v)) i = _
  conv_lhs => rw [← fiber_sum (B (fiberInclude j v))]
  simp only [map_sum,LinearMap.sum_apply,Module.End.mul_apply]
  change (WithLp.linearEquiv 2 ℂ (I → W)) (∑ x, A (fiberInclude x (B (fiberInclude j v) x))) i = _
  rw [map_sum,Finset.sum_apply]
  rfl

omit [Fintype I] [FiniteDimensional ℂ W] in
lemma hilbertBlock_one (i j : I) : hilbertBlock (1 : HW →ₗ[ℂ] HW) i j = if i=j then 1 else 0 := by
  ext v
  change fiberInclude j v i = _
  rw [fiberInclude_apply]
  split_ifs <;> rfl

omit [Fintype I] [DecidableEq I] [FiniteDimensional ℂ W] in
lemma hilbertBlock_sum {J : Type*} (s : Finset J) (A : J → HW →ₗ[ℂ] HW) (i j : I) :
    hilbertBlock (∑a∈s,A a) i j = ∑a∈s,hilbertBlock (A a) i j := by
  ext v
  simp [hilbertBlock,LinearMap.sum_apply,LinearMap.comp_apply,map_sum]

omit [Fintype I] [DecidableEq I] [FiniteDimensional ℂ W] in
lemma hilbertBlock_smul (r : ℝ) (A : HW →ₗ[ℂ] HW) (i j : I) :
    hilbertBlock (r • A) i j=r • hilbertBlock A i j := by
  ext v
  simp [hilbertBlock]

lemma fiber_adjoint (i : I) : (fiberInclude i : W →ₗ[ℂ] HW).adjoint=fiberProject i := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,fiberInclude_apply,apply_ite,inner_zero_right]
  change _ = ∑j, if j=i then inner ℂ (x j) y else 0
  simp only [fiberProject,LinearMap.comp_apply,LinearMap.proj_apply,LinearEquiv.coe_coe,
    WithLp.coe_linearEquiv,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma hilbertBlock_adjoint (A : HW →ₗ[ℂ] HW) (i j : I) :
    hilbertBlock A.adjoint i j=(hilbertBlock A j i).adjoint := by
  unfold hilbertBlock
  rw [LinearMap.adjoint_comp,LinearMap.adjoint_comp,fiber_adjoint,
    ← fiber_adjoint (W:=W) j,LinearMap.adjoint_adjoint]
  rfl

def hilbertBlocksHom : (HW →ₗ[ℂ] HW) →* Matrix I I (W →ₗ[ℂ] W) where
  toFun A := hilbertBlock A
  map_one' := by funext i j; exact hilbertBlock_one i j
  map_mul' A B := by funext i j; exact hilbertBlock_mul A B i j

omit [DecidableEq I] in
lemma trace_hilbertBlocks (A : HW →ₗ[ℂ] HW) :
    LinearMap.trace ℂ HW A = ∑i, LinearMap.trace ℂ W (hilbertBlock A i i) := by
  conv_lhs => rw [← mul_one A,← fiber_identity]
  rw [Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change LinearMap.trace ℂ HW ((A.comp (fiberInclude i)).comp (fiberProject i)) = _
  rw [LinearMap.trace_comp_comm']
  rfl

lemma trace_hilbertBlocks_prod {n : ℕ} (A : Fin (n+1) → HW →ₗ[ℂ] HW) :
    LinearMap.trace ℂ HW (List.ofFn A).prod =
      ∑x : Fin (n+1) → I, LinearMap.trace ℂ W
        (List.ofFn (fun j => hilbertBlock (A j) (x j) (x (finRotate (n+1) j)))).prod := by
  rw [trace_hilbertBlocks]
  rw [← map_sum]
  change LinearMap.trace ℂ W (Matrix.trace (hilbertBlocksHom (I:=I) (W:=W) (List.ofFn A).prod)) = _
  have hm := (hilbertBlocksHom (I:=I) (W:=W)).map_list_prod (List.ofFn A)
  rw [List.map_ofFn] at hm
  rw [hm,trace_prod_eq_sum_cycles,map_sum]
  rfl

theorem hilbert_block_trace_holder {q : ℕ} (hq : 0<q) (A : Fin (2*q) → HW →ₗ[ℂ] HW) :
    ‖LinearMap.trace ℂ HW (List.ofFn A).prod‖ ≤
      ∑x : Fin (2*q) → I, ∏j,
        evenMoment q (hilbertBlock (A j) (x j) (x (finRotate (2*q) j)))^(((2*q:ℕ):ℝ)⁻¹) := by
  have ht : LinearMap.trace ℂ HW (List.ofFn A).prod =
      ∑x : Fin (2*q) → I, LinearMap.trace ℂ W
        (List.ofFn (fun j => hilbertBlock (A j) (x j) (x (finRotate (2*q) j)))).prod := by
    generalize hm : 2*q=m at A ⊢
    cases m with
    | zero => omega
    | succ n => exact trace_hilbertBlocks_prod A
  rw [ht]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => linear_trace_holder hq _))

theorem evenMoment_blocks_le {q : ℕ} (hq : 0<q) (K : HW →ₗ[ℂ] HW) :
    evenMoment q K ≤ ∑x : Fin (2*q) → I, ∏j,
      (if j.val%2=0 then
        evenMoment q (hilbertBlock K (x (finRotate (2*q) j)) (x j))
      else evenMoment q (hilbertBlock K (x j) (x (finRotate (2*q) j))))^(((2*q:ℕ):ℝ)⁻¹) := by
  have ht := hilbert_block_trace_holder hq
    (fun j : Fin (2*q) => if j.val%2=0 then K.adjoint else K)
  rw [alternating_prod] at ht
  refine (Complex.re_le_norm _).trans (ht.trans_eq ?_)
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> simp only [hilbertBlock_adjoint,evenMoment_adjoint]

end BinaryCoordinateSweeps.Irrep

end

end OAI
