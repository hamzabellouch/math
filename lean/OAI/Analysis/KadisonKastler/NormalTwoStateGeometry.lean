import OAI.Analysis.KadisonKastler.NormalTwoStateSupports

namespace OAI

/-! # Concrete corners of the two-representation Hilbert space -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
  (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))

def normalTwoStateSlot (i j : Fin 2) (a : Algebra M) :
    TwoStateMatrixHilbert H K →L[ℂ] TwoStateMatrixHilbert H K :=
  (normalTwoStateEquiv θ hθ (matrixSlot i j a)).val

theorem normalTwoStateSlot_mul (i j k : Fin 2) (a b : Algebra M) :
    normalTwoStateSlot θ hθ i j a * normalTwoStateSlot θ hθ j k b =
      normalTwoStateSlot θ hθ i k (a * b) := by
  have h := (normalTwoStateEquiv θ hθ).toStarAlgHom.map_mul'
    (matrixSlot i j a) (matrixSlot j k b)
  exact (congrArg Subtype.val h).symm.trans
    (congrArg (fun x => (normalTwoStateEquiv θ hθ x).val) (matrixSlot_mul i j k a b))

theorem normalTwoStateSlot_star (i j : Fin 2) (a : Algebra M) :
    star (normalTwoStateSlot θ hθ i j a) = normalTwoStateSlot θ hθ j i (star a) := by
  have h := (normalTwoStateEquiv θ hθ).toStarAlgHom.map_star' (matrixSlot i j a)
  exact (congrArg Subtype.val h).symm.trans
    (congrArg (fun x => (normalTwoStateEquiv θ hθ x).val) (matrixSlot_star i j a))

theorem normalTwoStateSlot_fst (i j r : Fin 2) (a : Algebra M)
    (x : TwoStateMatrixHilbert H K) :
    (normalTwoStateSlot θ hθ i j a x).fst r = if r = i then a.val (x.fst j) else 0 := by
  change ((normalTwoStateEquiv θ hθ (matrixSlot i j a)).val x).fst r = _
  rw [normalTwoStateEquiv_coe]
  change matrixOperatorHom M (matrixSlot i j a) x.fst r = _
  fin_cases i <;> fin_cases j <;> fin_cases r <;>
    simp [matrixOperatorHom_apply, hilbertMatrix_apply, matrixSlot,
      Fin.sum_univ_two, CStarMatrix.map_apply]

theorem normalTwoStateSlot_snd (i j r : Fin 2) (a : Algebra M)
    (x : TwoStateMatrixHilbert H K) :
    (normalTwoStateSlot θ hθ i j a x).snd r = if r = i then (θ a).val (x.snd j) else 0 := by
  change ((normalTwoStateEquiv θ hθ (matrixSlot i j a)).val x).snd r = _
  rw [normalTwoStateEquiv_coe]
  change matrixOperatorHom N (coefficientMatrixMap θ.toStarAlgHom (matrixSlot i j a)) x.snd r = _
  fin_cases i <;> fin_cases j <;> fin_cases r <;>
    simp [matrixOperatorHom_apply, hilbertMatrix_apply, matrixSlot,
      Fin.sum_univ_two, CStarMatrix.map_apply, coefficientMatrixMap_apply]

def twoStateSourceEmbedding : H →ₗᵢ[ℂ] TwoStateMatrixHilbert H K where
  toFun x := WithLp.toLp 2 (tupleSingle 0 x, 0)
  map_add' x y := by simp [map_add, ← WithLp.toLp_add]
  map_smul' z x := by simp [map_smul, ← WithLp.toLp_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp

def twoStateTargetEmbedding : K →ₗᵢ[ℂ] TwoStateMatrixHilbert H K where
  toFun x := WithLp.toLp 2 (0, tupleSingle 1 x)
  map_add' x y := by simp [map_add, ← WithLp.toLp_add]
  map_smul' z x := by simp [map_smul, ← WithLp.toLp_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp

@[simp] theorem twoStateSourceEmbedding_adjoint (x : TwoStateMatrixHilbert H K) :
    (twoStateSourceEmbedding (H := H) (K := K)).toContinuousLinearMap.adjoint x = x.fst 0 := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [twoStateSourceEmbedding, WithLp.prod_inner_apply, PiLp.inner_apply,
    tupleSingle_apply, Fin.sum_univ_two]

@[simp] theorem twoStateTargetEmbedding_adjoint (x : TwoStateMatrixHilbert H K) :
    (twoStateTargetEmbedding (H := H) (K := K)).toContinuousLinearMap.adjoint x = x.snd 1 := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [twoStateTargetEmbedding, WithLp.prod_inner_apply, PiLp.inner_apply,
    tupleSingle_apply, Fin.sum_univ_two]

theorem twoStateSourceEmbedding_rangeProjection :
    (twoStateSourceEmbedding (H := H) (K := K)).toContinuousLinearMap.comp
      (twoStateSourceEmbedding (H := H) (K := K)).toContinuousLinearMap.adjoint =
        normalTwoStateSlot θ hθ 0 0 1 * twoStateSummandProjection 0 := by
  ext x
  change twoStateSourceEmbedding
    ((twoStateSourceEmbedding (H := H) (K := K)).toContinuousLinearMap.adjoint x) = _
  rw [twoStateSourceEmbedding_adjoint]
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> apply PiLp.ext <;> intro r
  · change (tupleSingle 0 (x.fst 0)) r =
      (normalTwoStateSlot θ hθ 0 0 1 (twoStateSummandProjection 0 x)).fst r
    rw [normalTwoStateSlot_fst]
    fin_cases r <;> simp [twoStateSummandProjection, tupleSingle_apply]
  · change (0 : FiniteHilbert (Fin 2) K) r =
      (normalTwoStateSlot θ hθ 0 0 1 (twoStateSummandProjection 0 x)).snd r
    rw [normalTwoStateSlot_snd]
    simp [twoStateSummandProjection]

theorem twoStateTargetEmbedding_rangeProjection :
    (twoStateTargetEmbedding (H := H) (K := K)).toContinuousLinearMap.comp
      (twoStateTargetEmbedding (H := H) (K := K)).toContinuousLinearMap.adjoint =
        normalTwoStateSlot θ hθ 1 1 1 * twoStateSummandProjection 1 := by
  ext x
  change twoStateTargetEmbedding
    ((twoStateTargetEmbedding (H := H) (K := K)).toContinuousLinearMap.adjoint x) = _
  rw [twoStateTargetEmbedding_adjoint]
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> apply PiLp.ext <;> intro r
  · change (0 : FiniteHilbert (Fin 2) H) r =
      (normalTwoStateSlot θ hθ 1 1 1 (twoStateSummandProjection 1 x)).fst r
    rw [normalTwoStateSlot_fst]
    simp [twoStateSummandProjection]
  · change (tupleSingle 1 (x.snd 1)) r =
      (normalTwoStateSlot θ hθ 1 1 1 (twoStateSummandProjection 1 x)).snd r
    rw [normalTwoStateSlot_snd]
    fin_cases r <;> simp [twoStateSummandProjection, tupleSingle_apply]

end

end KadisonKastler

end OAI
