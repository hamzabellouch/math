import OAI.Analysis.PlanarPacking.FiniteInverse
import OAI.Analysis.PlanarPacking.FiniteU
import OAI.Analysis.PlanarPacking.FiniteTail
import OAI.Analysis.PlanarPacking.FiniteSplit
import OAI.Analysis.PlanarPacking.FiniteLift

namespace OAI

/-!
# The finite interpolation system

Schur complements give existence, uniqueness and norm bounds for the finite system.
-/

namespace SharpPlanar.Numerical
noncomputable def signedS (neg : Bool) : X →L[ℝ] X := if neg then -S else S
noncomputable def centralV (neg : Bool) : L1Finite (Fin 6) →L[ℝ] L1Finite (Fin 6) :=
  if neg then inverseMinusEquiv.toContinuousLinearMap else inversePlusEquiv.toContinuousLinearMap
noncomputable def signedU (neg : Bool) := RJ.comp ((signedS neg).comp IE)
noncomputable def signedL (neg : Bool) := RE.comp ((signedS neg).comp IJ)
noncomputable def signedE (neg : Bool) := RE.comp ((signedS neg).comp IE)
noncomputable def finiteA (neg : Bool) : L1Finite FiniteIndex →L[ℝ] L1Finite FiniteIndex :=
  1-RF.comp ((signedS neg).comp IF)
lemma compressed_D : RJ.comp (S.comp IJ) = matrixL1 Dmat := by
  rw [compressed_S_matrix]; rfl
lemma compressed_U : RJ.comp (S.comp IE) = matrixL1 Umat := by
  rw [compressed_S_matrix]; rfl
lemma centralV_norm (neg : Bool) : ‖centralV neg‖ ≤ 32 := by
  cases neg
  · exact inversePlus_norm.le
  · exact inverseMinus_norm.le
lemma signedVU_norm (neg : Bool) : ‖(centralV neg).comp (signedU neg)‖ ≤ (37:ℝ)/10 := by
  cases neg
  · exact (by simpa only [centralV,signedU,signedS,Bool.false_eq_true,ite_false,compressed_U] using inversePlus_U_norm.le)
  · simpa only [centralV,signedU,signedS,ite_true,ContinuousLinearMap.neg_comp,
      ContinuousLinearMap.comp_neg,compressed_U,norm_neg] using inverseMinus_U_norm.le
lemma signedL_norm (neg : Bool) : ‖signedL neg‖ ≤ (11:ℝ)/100 := by
  cases neg <;> simpa only [signedL,signedS,Bool.false_eq_true,ite_false,ite_true,
    ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,norm_neg] using exterior_central_norm
lemma signedE_norm (neg : Bool) : ‖signedE neg‖ ≤ (28:ℝ)/100 := by
  cases neg <;> simpa only [signedE,signedS,Bool.false_eq_true,ite_false,ite_true,
    ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,norm_neg] using exterior_exterior_norm
lemma signedS_norm (neg : Bool) : ‖signedS neg‖ ≤ 28 := by
  cases neg <;> simpa only [signedS,Bool.false_eq_true,ite_false,ite_true,norm_neg] using norm_S_le
lemma centralV_left (neg : Bool) (x : L1Finite (Fin 6)) :
    centralV neg (x-RJ (signedS neg (IJ x))) = x := by
  have hD (y : L1Finite (Fin 6)) : RJ (S (IJ y)) = matrixL1 Dmat y :=
    congrArg (fun f => f y) compressed_D
  cases neg
  · change inversePlusEquiv (x-RJ (S (IJ x))) = x
    rw [hD]
    have hh := (certifiedEquiv (matrixL1 Aplus) (matrixL1 Wplus) defectplus_lt_one).symm_apply_apply x
    change inversePlusEquiv (matrixL1 Aplus x) = x at hh
    simpa only [Aplus,matrixL1_sub,matrixL1_one,sub_apply,one_apply_eq_self] using hh
  · change inverseMinusEquiv (x-RJ (-S (IJ x))) = x
    rw [map_neg,hD,sub_neg_eq_add]
    have hh := (certifiedEquiv (matrixL1 Aminus) (matrixL1 Wminus) defectminus_lt_one).symm_apply_apply x
    change inverseMinusEquiv (matrixL1 Aminus x) = x at hh
    have he : matrixL1 Aminus x = x+matrixL1 Dmat x := by
      ext i
      simp [Aminus,matrixL1_apply,Matrix.add_apply,Matrix.one_apply,add_mul,Finset.sum_add_distrib]
    rw [he] at hh
    exact hh
lemma finiteA_left (neg : Bool) (x : L1Finite FiniteIndex) :
    l1Left (finiteA neg x) = l1Left x - RJ (signedS neg (IJ (l1Left x))) - signedU neg (l1Right x) := by
  have hs := finiteEmbedding_split x
  change IF x = IJ (l1Left x)+IE (l1Right x) at hs
  ext i
  change x (Sum.inl i) - RF (signedS neg (IF x)) (Sum.inl i) = _
  rw [hs,map_add,map_add]
  change x (Sum.inl i) - (RJ (signedS neg (IJ (l1Left x))) i + RJ (signedS neg (IE (l1Right x))) i) = _
  change _ = x (Sum.inl i)-RJ (signedS neg (IJ (l1Left x))) i - RJ (signedS neg (IE (l1Right x))) i
  ring
lemma finiteA_right (neg : Bool) (x : L1Finite FiniteIndex) :
    l1Right (finiteA neg x) = l1Right x - signedL neg (l1Left x) - signedE neg (l1Right x) := by
  have hs := finiteEmbedding_split x
  change IF x = IJ (l1Left x)+IE (l1Right x) at hs
  ext i
  change x (Sum.inr i) - RF (signedS neg (IF x)) (Sum.inr i) = _
  rw [hs,map_add,map_add]
  change x (Sum.inr i) - (RE (signedS neg (IJ (l1Left x))) i + RE (signedS neg (IE (l1Right x))) i) = _
  change _ = x (Sum.inr i)-RE (signedS neg (IJ (l1Left x))) i - RE (signedS neg (IE (l1Right x))) i
  ring
lemma finiteA_coercive (neg : Bool) (x : L1Finite FiniteIndex) : ‖x‖ ≤ 90*‖finiteA neg x‖ := by
  rw [l1Split_norm x,l1Split_norm (finiteA neg x)]
  apply finite_schur_bound (centralV neg) (signedU neg) (signedL neg) (signedE neg)
    (centralV_norm neg) (signedE_norm neg) (signedL_norm neg) (signedVU_norm neg)
  · rw [finiteA_left,sub_add_cancel,centralV_left]
  · exact (finiteA_right neg x).symm
lemma finiteA_bijective (neg : Bool) : Function.Bijective (finiteA neg) := by
  have hi : Function.Injective (finiteA neg) := by
    intro x y hxy
    have hb := finiteA_coercive neg (x-y)
    rw [map_sub,hxy,sub_self,norm_zero,mul_zero] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
noncomputable def finiteEquiv (neg : Bool) : L1Finite FiniteIndex ≃L[ℝ] L1Finite FiniteIndex :=
  (LinearEquiv.ofBijective (finiteA neg).toLinearMap (finiteA_bijective neg)).toContinuousLinearEquiv
noncomputable def finiteV (neg : Bool) : L1Finite FiniteIndex →L[ℝ] L1Finite FiniteIndex :=
  (finiteEquiv neg).symm.toContinuousLinearMap
lemma finiteV_norm (neg : Bool) : ‖finiteV neg‖ ≤ 90 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hh := finiteA_coercive neg (finiteV neg x)
  have he : finiteA neg (finiteV neg x) = x := (finiteEquiv neg).apply_symm_apply x
  simpa only [he] using hh
lemma finiteV_left (neg : Bool) (x : L1Finite FiniteIndex) :
    finiteV neg (x - RF (signedS neg (IF x))) = x :=
  (finiteEquiv neg).symm_apply_apply x
lemma finiteV_right (neg : Bool) (x : L1Finite FiniteIndex) :
    finiteV neg x - RF (signedS neg (IF (finiteV neg x))) = x :=
  (finiteEquiv neg).apply_symm_apply x
lemma signed_discard (neg : Bool) (x : X) :
    ‖signedS neg x - IF (RF (signedS neg x))‖ ≤ (1:ℝ)/2000000000*‖x‖ := by
  cases neg
  · exact finite_discard_S x
  · change ‖-S x - IF (RF (-S x))‖ ≤ _
    rw [map_neg,map_neg,neg_sub_neg,norm_sub_rev]
    exact finite_discard_S x
lemma signed_discard_norm (neg : Bool) :
    ‖signedS neg - IF.comp (RF.comp (signedS neg))‖ ≤ (1:ℝ)/2000000000 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  exact signed_discard neg x

theorem interpolation_exists_unique (neg : Bool) (r : X) : ∃! x : X, x-signedS neg x=r := by
  exact finiteLift_exists_unique IF RF (signedS neg) (finiteV neg)
    (finiteV_left neg) (finiteV_right neg) (finiteEmbedding_norm_le _)
    (finiteRestriction_norm _ _) (signedS_norm neg) (finiteV_norm neg) (signed_discard_norm neg) r
theorem interpolation_norm_bound (neg : Bool) {x r : X} (hx : x-signedS neg x=r) :
    ‖x‖ ≤ 91*‖RF r‖+2540*‖r-IF (RF r)‖ := by
  apply finiteLift_estimate IF RF (signedS neg) (finiteV neg)
    (finiteV_left neg) (finiteEmbedding_norm_le _) (finiteRestriction_norm _ _)
    (signedS_norm neg) (finiteV_norm neg) (signed_discard_norm neg)
  rw [hx,add_sub_cancel]
end SharpPlanar.Numerical

end OAI
