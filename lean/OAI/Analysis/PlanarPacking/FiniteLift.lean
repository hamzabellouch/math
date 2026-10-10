import OAI.Analysis.PlanarPacking.Schur

namespace OAI

namespace SharpPlanar
section Lift
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


noncomputable def liftedInverse (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F) : E →L[ℝ] E :=
  1 + I.comp (V.comp (R.comp S))

lemma liftedInverse_apply (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F) (x : E) :
    liftedInverse I R S V x = x + I (V (R (S x))) := rfl

lemma liftedInverse_left (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hVA : ∀ y, V (y - R (S (I y))) = y) (x : E) :
    liftedInverse I R S V (x-I (R (S x))) = x := by
  rw [liftedInverse_apply,map_sub,map_sub,hVA]
  abel

lemma liftedInverse_right (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hAV : ∀ y, V y - R (S (I (V y))) = y) (x : E) :
    liftedInverse I R S V x - I (R (S (liftedInverse I R S V x))) = x := by
  rw [liftedInverse_apply,map_add,map_add,map_add]
  have h := congrArg I (hAV (R (S x)))
  rw [map_sub] at h
  calc
    _ = x + (I (V (R (S x))) - I (R (S (I (V (R (S x)))))) - I (R (S x))) := by abel
    _ = x := by rw [h]; simp

lemma liftedInverse_finite (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hVA : ∀ y, V (y - R (S (I y))) = y) (y : F) :
    liftedInverse I R S V (I y) = I (V y) := by
  rw [liftedInverse_apply]
  have h := congrArg I (hVA y)
  simp only [map_sub] at h
  calc
    _ = (I (V y) - I (V (R (S (I y))))) + I (V (R (S (I y)))) := by rw [h]
    _ = _ := by abel

lemma liftedInverse_norm (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hI : ‖I‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hS : ‖S‖ ≤ 28) (hV : ‖V‖ ≤ 90) :
    ‖liftedInverse I R S V‖ ≤ 2521 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [liftedInverse_apply]
  calc
    ‖x + I (V (R (S x)))‖ ≤ ‖x‖ + ‖I (V (R (S x)))‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ‖I‖*(‖V‖*(‖R‖*(‖S‖*‖x‖))) := by
      gcongr
      exact (I.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((V.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          ((R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)))
          (norm_nonneg _))) (norm_nonneg _))
    _ ≤ ‖x‖ + 1*(90*(1*(28*‖x‖))) := by gcongr
    _ = 2521*‖x‖ := by ring


theorem finiteLift_exists_unique [CompleteSpace E]
    (I : F →L[ℝ] E) (R : E →L[ℝ] F) (S : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hVA : ∀ y, V (y - R (S (I y))) = y)
    (hAV : ∀ y, V y - R (S (I (V y))) = y)
    (hI : ‖I‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hS : ‖S‖ ≤ 28) (hV : ‖V‖ ≤ 90)
    (htail : ‖S-I.comp (R.comp S)‖ ≤ 1/2000000000) (r : E) :
    ∃! x : E, x-S x = r := by
  let B := liftedInverse I R S V
  let T := B.comp (S-I.comp (R.comp S))
  have hB : ‖B‖ ≤ 2521 := liftedInverse_norm I R S V hI hR hS hV
  have hT : ‖T‖ ≤ 2521/2000000000 := calc
    ‖T‖ ≤ ‖B‖*‖S-I.comp (R.comp S)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2521*(1/2000000000) := by gcongr
    _ = _ := by ring
  have hBinj : Function.Injective B := by
    intro x y he
    have hx := liftedInverse_right I R S V hAV x
    have hy := liftedInverse_right I R S V hAV y
    rw [show liftedInverse I R S V x = liftedInverse I R S V y from he] at hx
    exact hx.symm.trans hy
  have heq (x : E) : B (x-S x) = x-T x := by
    have hx := liftedInverse_left I R S V hVA x
    change B (x-I (R (S x))) = x at hx
    simp only [map_sub] at hx
    change B (x - S x) = x - B (S x - I (R (S x)))
    simp only [map_sub]
    calc
      _ = (B x - B (I (R (S x)))) - (B (S x) - B (I (R (S x)))) := by abel
      _ = _ := by rw [hx]
  obtain ⟨x,hx,hu⟩ := neumann_exists_unique T (hT.trans_lt (by norm_num)) (B r)
  refine ⟨x, hBinj (by rw [heq]; exact hx), ?_⟩
  intro y hy
  apply hu
  rw [← heq,hy]


theorem finiteLift_estimate
    (I : F →L[ℝ] E) (R : E →L[ℝ] F) (S : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hVA : ∀ y, V (y - R (S (I y))) = y)
    (hI : ‖I‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hS : ‖S‖ ≤ 28) (hV : ‖V‖ ≤ 90)
    (htail : ‖S-I.comp (R.comp S)‖ ≤ 1/2000000000)
    {x rt : E} {rf : F} (hx : x-S x = I rf+rt) :
    ‖x‖ ≤ 91*‖rf‖+2540*‖rt‖ := by
  let B := liftedInverse I R S V
  let T := B.comp (S-I.comp (R.comp S))
  have hB : ‖B‖ ≤ 2521 := liftedInverse_norm I R S V hI hR hS hV
  have hT : ‖T‖ ≤ 2521/2000000000 := calc
    ‖T‖ ≤ ‖B‖*‖S-I.comp (R.comp S)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2521*(1/2000000000) := by gcongr
    _ = _ := by ring
  have heq : x-T x = B (I rf+rt) := by
    rw [← hx]
    have hh := liftedInverse_left I R S V hVA x
    change B (x-I (R (S x))) = x at hh
    simp only [map_sub] at hh
    change x - B (S x-I (R (S x))) = B (x-S x)
    simp only [map_sub]
    calc
      _ = (B x-B (I (R (S x))))-(B (S x)-B (I (R (S x)))) := by rw [hh]
      _ = _ := by abel
  have hn : ‖B (I rf+rt)‖ ≤ 90*‖rf‖+2521*‖rt‖ := by
    rw [map_add]
    change ‖liftedInverse I R S V (I rf)+B rt‖ ≤ _
    rw [liftedInverse_finite I R S V hVA]
    calc
      _ ≤ ‖I (V rf)‖+‖B rt‖ := norm_add_le _ _
      _ ≤ ‖I‖*(‖V‖*‖rf‖)+‖B‖*‖rt‖ := by
        gcongr
        exacts [(I.le_opNorm _).trans (mul_le_mul_of_nonneg_left (V.le_opNorm _) (norm_nonneg _)), B.le_opNorm _]
      _ ≤ 1*(90*‖rf‖)+2521*‖rt‖ := by gcongr
      _ = _ := by ring
  have hb := neumann_norm_bound T (by norm_num : (2521:ℝ)/2000000000 < 1) hT heq
  apply hb.trans
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<1-2521/2000000000)).mpr
  nlinarith [norm_nonneg rf,norm_nonneg rt]
end Lift
end SharpPlanar

end OAI
