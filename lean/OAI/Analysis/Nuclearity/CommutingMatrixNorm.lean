import OAI.Analysis.Nuclearity.CommutingMatrixPositive

namespace OAI

/-! A dimension-independent bound for the commuting matrix tensor map.
Only positivity and its value on the identity are used. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]
  [PartialOrder C] [StarOrderedRing C] [PartialOrder D] [StarOrderedRing D]

def commutingMatrixPositiveMap {n : ℕ} (hn : 1 ≤ n)
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] D) (hψ : CompletelyPositive ψ)
    (η : C →⋆ₐ[ℂ] D) (hc : ∀ i j c, Commute (ψ (matrixUnit i j)) (η c)) :
    CStarMatrix (Fin n) (Fin n) C →ₚ[ℂ] D :=
  PositiveLinearMap.mk₀ (commutingMatrixLinearMap ψ η.toNonUnitalStarAlgHom)
    (commutingMatrixLinearMap_nonneg hn ψ hψ η.toNonUnitalStarAlgHom hc)

lemma commutingMatrixPositiveMap_one {n : ℕ} (hn : 1 ≤ n)
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] D) (hψ : CompletelyPositive ψ)
    (η : C →⋆ₐ[ℂ] D) (hc : ∀ i j c, Commute (ψ (matrixUnit i j)) (η c)) :
    commutingMatrixPositiveMap hn ψ hψ η hc 1 = ψ 1 := by
  change (∑ i, ∑ j, ψ (matrixUnit i j) * η ((1 : CStarMatrix (Fin n) (Fin n) C) i j)) = _
  have he (i j : Fin n) : ψ (matrixUnit i j) * η ((1 : CStarMatrix (Fin n) (Fin n) C) i j) =
      (1 : CStarMatrix (Fin n) (Fin n) ℂ) i j • ψ (matrixUnit i j) := by
    by_cases hij : i = j
    · subst j
      simp only [CStarMatrix.one_apply, ite_true, map_one, mul_one, one_smul]
    · simp only [CStarMatrix.one_apply, hij, ite_false, map_zero, mul_zero, zero_smul]
  simp_rw [he]
  conv_rhs => rw [← matrix_unit_expansion (1 : CStarMatrix (Fin n) (Fin n) ℂ)]
  simp only [map_sum, map_smul]

lemma positiveLinearMap_norm_four_bound {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    [PartialOrder E] [StarOrderedRing E] [PartialOrder F] [StarOrderedRing F]
    (f : E →ₚ[ℂ] F) (x : E) : ‖f x‖ ≤ (4 * ‖f 1‖) * ‖x‖ := by
  obtain ⟨a, ha, han, he⟩ := CStarAlgebra.exists_sum_four_nonneg x
  calc
    ‖f x‖ = ‖∑ i : Fin 4, Complex.I ^ (i : ℕ) • f (a i)‖ := by
      rw [he]
      simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin 4, ‖Complex.I ^ (i : ℕ) • f (a i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖f 1‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      simp only [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      exact (f.norm_apply_le_of_nonneg _ (ha i)).trans
        (mul_le_mul_of_nonneg_left (han i) (norm_nonneg _))
    _ = _ := by simp; ring

lemma commutingMatrixLinearMap_norm_le {n : ℕ} (hn : 1 ≤ n)
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] D) (hψ : CompletelyPositive ψ)
    (η : C →⋆ₐ[ℂ] D) (hc : ∀ i j c, Commute (ψ (matrixUnit i j)) (η c))
    (M : CStarMatrix (Fin n) (Fin n) C) :
    ‖commutingMatrixLinearMap ψ η.toNonUnitalStarAlgHom M‖ ≤ (4 * ‖ψ‖) * ‖M‖ := by
  have h := positiveLinearMap_norm_four_bound (commutingMatrixPositiveMap hn ψ hψ η hc) M
  rw [commutingMatrixPositiveMap_one] at h
  apply h.trans
  have h1 : ‖ψ 1‖ ≤ ‖ψ‖ := by
    let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    simpa only [norm_one, mul_one] using ψ.le_opNorm 1
  gcongr

omit [PartialOrder C] [StarOrderedRing C] [PartialOrder D] [StarOrderedRing D] in
lemma commutingMatrixLinearMap_coefficient {n : ℕ}
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] D)
    (η : C →⋆ₐ[ℂ] D) (M : CStarMatrix (Fin n) (Fin n) ℂ) (c : C) :
    commutingMatrixLinearMap ψ η.toNonUnitalStarAlgHom (matrixTensorCoefficient M c) =
      ψ M * η c := by
  change (∑ i, ∑ j, ψ (matrixUnit i j) * η (M i j • c)) = _
  simp only [map_smul, mul_smul_comm]
  conv_rhs => rw [← matrix_unit_expansion M]
  simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]

end WeakPureInfiniteness

end

end OAI
