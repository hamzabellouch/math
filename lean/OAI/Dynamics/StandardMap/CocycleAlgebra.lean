import OAI.Dynamics.StandardMap.GridAtomBound

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma transferProduct_concat (v : ℕ → ℝ) (m n : ℕ) :
    transferProduct v (m+n)=(transferProduct (fun i => v (m+i)) n).comp (transferProduct v m) := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
    rw [show m+(n+1)=(m+n)+1 by omega,transferProduct,ih,transferProduct]
    simp only [ContinuousLinearMap.comp_assoc,Nat.add_assoc]
lemma torusSegmentCoefficient_shift (k : ℝ) (z : Torus) (a : ℤ) (m : ℕ) :
    (fun i => torusSegmentCoefficient k z a (m+i))=torusSegmentCoefficient k z (a+(m:ℤ)) := by
  funext i
  unfold torusSegmentCoefficient
  congr 3
  push_cast
  ring
lemma torusSegmentTransfer_concat (k : ℝ) (z : Torus) (a : ℤ) (m n : ℕ) :
    torusSegmentTransfer k z a (m+n)=
      (torusSegmentTransfer k z (a+(m:ℤ)) n).comp (torusSegmentTransfer k z a m) := by
  unfold torusSegmentTransfer
  rw [transferProduct_concat,torusSegmentCoefficient_shift]
lemma torusSegmentTransfer_shift (k : ℝ) (z : Torus) (a b : ℤ) (n : ℕ) :
    torusSegmentTransfer k (torusIter k b z) a n=torusSegmentTransfer k z (a+b) n := by
  unfold torusSegmentTransfer
  congr 1
  funext i
  unfold torusSegmentCoefficient
  rw [← torusIter_add]
  congr 3
  ring
lemma torusIter_neg_swap (k : ℝ) (n : ℕ) (z : Torus) :
    torusIter k (-(n:ℤ)) z=(torusIter k (n:ℤ) z.swap).swap := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ((n+1:ℕ):ℤ)=1+(n:ℤ) by omega,show -(1+(n:ℤ))=(-1)+(-(n:ℤ)) by ring,
      torusIter_add,torusIter_add,ih]
    simp only [torusIter,zpow_neg_one,zpow_one,Equiv.Perm.inv_def,torusStep_symm_apply,torusStep_apply,
      recurrenceMap,Prod.fst_swap,Prod.snd_swap,Prod.swap_prod_mk]
noncomputable def planeSwap : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨z.im,z.re⟩
        map_add' := by intro z w; apply Complex.ext <;> simp
        map_smul' := by intro t z; apply Complex.ext <;> simp }
    cont := Complex.equivRealProdCLM.symm.continuous.comp
      (Complex.continuous_im.prodMk Complex.continuous_re) }
@[simp] lemma planeSwap_re (z : ℂ) : (planeSwap z).re=z.im := rfl
@[simp] lemma planeSwap_im (z : ℂ) : (planeSwap z).im=z.re := rfl
@[simp] lemma planeSwap_invol (z : ℂ) : planeSwap (planeSwap z)=z := by apply Complex.ext <;> rfl
@[simp] lemma norm_planeSwap (z : ℂ) : ‖planeSwap z‖=‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm,Complex.normSq_apply,planeSwap_re,planeSwap_im]
  ring
lemma norm_comp_planeSwap (A : ℂ →L[ℝ] ℂ) : ‖A.comp planeSwap‖=‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,norm_planeSwap] using A.le_opNorm (planeSwap z)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,planeSwap_invol,norm_planeSwap] using
      (A.comp planeSwap).le_opNorm (planeSwap z)
lemma norm_planeSwap_comp (A : ℂ →L[ℝ] ℂ) : ‖planeSwap.comp A‖=‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,norm_planeSwap] using A.le_opNorm z
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,norm_planeSwap] using (planeSwap.comp A).le_opNorm z
lemma planeSwap_transferStep (v : ℝ) (z : ℂ) :
    planeSwap (transferStep v (planeSwap z))=transferStepInv v z := by apply Complex.ext <;> rfl
lemma torus_backward_pair_coordinate (k : ℝ) (z : Torus) (n : ℕ) :
    (torusIter k (-(n:ℤ)-1) z).1=(torusIter k (n:ℤ) z.swap).1 := by
  rw [show -(n:ℤ)-1=(-1)+(-(n:ℤ)) by ring,torusIter_add,torusIter_neg_swap]
  rfl
lemma torusSegmentTransfer_reverse_identity (k : ℝ) (z : Torus) (n : ℕ) (u : ℂ) :
    torusSegmentTransfer k z (-(n:ℤ)) n
      (planeSwap (torusSegmentTransfer k z.swap 0 n (planeSwap u)))=u := by
  induction n generalizing u with
  | zero => simp [torusSegmentTransfer,transferProduct]
  | succ n ih =>
    have hc : torusSegmentTransfer k z (-((n+1:ℕ):ℤ)) (n+1)=
        (torusSegmentTransfer k z (-(n:ℤ)) n).comp
          (transferStep (torusPotential k (torusIter k (-(n:ℤ)-1) z).1)) := by
      rw [show n+1=1+n by omega,torusSegmentTransfer_concat]
      congr 1
      · congr 1; push_cast; ring
      · simp only [torusSegmentTransfer,transferProduct,ContinuousLinearMap.comp_id,
          torusSegmentCoefficient]
        exact congrArg (fun t : ℤ => transferStep (torusPotential k (torusIter k t z).1)) (by omega)
    rw [hc]
    change torusSegmentTransfer k z (-(n:ℤ)) n
      (transferStep (torusPotential k (torusIter k (-(n:ℤ)-1) z).1)
        (planeSwap (transferStep (torusSegmentCoefficient k z.swap 0 (n+1))
          (torusSegmentTransfer k z.swap 0 n (planeSwap u)))))=u
    have hcoef : torusSegmentCoefficient k z.swap 0 (n+1)=
        torusPotential k (torusIter k (-(n:ℤ)-1) z).1 := by
      unfold torusSegmentCoefficient
      rw [show (0:ℤ)+((n+1:ℕ):ℤ)-1=(n:ℤ) by omega,torus_backward_pair_coordinate]
    rw [hcoef]
    have he (v : ℝ) (w : ℂ) : transferStep v (planeSwap (transferStep v w))=planeSwap w := by
      apply Complex.ext <;> simp
    rw [he]
    exact ih u
lemma torusSegmentTransfer_reverse_norm (k : ℝ) (z : Torus) (n : ℕ) :
    ‖torusSegmentTransfer k z.swap 0 n‖=‖torusSegmentTransfer k z (-(n:ℤ)) n‖ := by
  let A := torusSegmentTransfer k z (-(n:ℤ)) n
  let B := (planeSwap.comp (torusSegmentTransfer k z.swap 0 n)).comp planeSwap
  have hAB : ∀ u, A (B u)=u := torusSegmentTransfer_reverse_identity k z n
  have he : B=transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n := by
    ext u
    apply (show Function.Injective A from fun x y hxy => by
      have := congrArg (transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n) hxy
      simpa only [A,torusSegmentTransfer,transferProductInv_inverse] using this)
    rw [hAB]
    exact (transferProduct_inverse _ _ _).symm
  have hnorm : ‖B‖=‖torusSegmentTransfer k z.swap 0 n‖ := by
    dsimp only [B]
    rw [norm_comp_planeSwap,norm_planeSwap_comp]
  rw [← hnorm,he,← transferProduct_norm_inverse]
  rfl
end StandardMapEntropy

end OAI
