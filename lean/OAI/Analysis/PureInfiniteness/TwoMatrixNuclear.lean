import OAI.Analysis.Nuclearity.MatrixCPAmplification

namespace OAI

/-! The two-by-two nuclearity specialization used by the doubled-corner
application. Matrix errors are controlled by continuity on finitely many
entries; the completely positive approximations remain contractions. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder A] [StarOrderedRing A]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]

lemma completelyPositive_comp (φ : A →L[ℂ] B) (ψ : B →L[ℂ] C)
    (hφ : CompletelyPositive φ) (hψ : CompletelyPositive ψ) :
    CompletelyPositive (ψ.comp φ) := by
  intro n M hM
  exact hψ n _ (hφ n M hM)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma starHomContinuousLinear_norm_le_one (φ : A →⋆ₙₐ[ℂ] B) :
    ‖starHomContinuousLinear φ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  change ‖φ a‖ ≤ 1 * ‖a‖
  simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ a

def twoMatrixReindex (n : ℕ) :
    CStarMatrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ ≃⋆ₐ[ℂ]
      CStarMatrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  CStarMatrix.reindexₐ ℂ ℂ finProdFinEquiv

def twoMatrixPack (n : ℕ) : CStarMatrix (Fin 2) (Fin 2)
    (CStarMatrix (Fin n) (Fin n) ℂ) →⋆ₙₐ[ℂ] CStarMatrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  (twoMatrixReindex n).toStarAlgHom.toNonUnitalStarAlgHom.comp flattenCStarMatrix

def twoMatrixUnpack (n : ℕ) : CStarMatrix (Fin (2 * n)) (Fin (2 * n)) ℂ →⋆ₙₐ[ℂ]
    CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin n) (Fin n) ℂ) :=
  unflattenCStarMatrix.comp (twoMatrixReindex n).symm.toStarAlgHom.toNonUnitalStarAlgHom

lemma twoMatrixUnpack_pack (n : ℕ)
    (M : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin n) (Fin n) ℂ)) :
    twoMatrixUnpack n (twoMatrixPack n M) = M := by
  change unflattenCStarMatrix ((twoMatrixReindex n).symm
    (twoMatrixReindex n (flattenCStarMatrix M))) = M
  rw [StarAlgEquiv.symm_apply_apply, unflatten_flattenCStarMatrix]

local instance twoMatrixOrder : PartialOrder (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrder _
local instance twoMatrixOrdered : StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrderedRing _

def twoMatrixEntries (F : Finset (CStarMatrix (Fin 2) (Fin 2) A)) :
    (F × Fin 2 × Fin 2 → A) →L[ℂ] (F → CStarMatrix (Fin 2) (Fin 2) A) where
  toFun e M i j := e (M, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_pi fun M => continuous_pi fun i => continuous_pi fun j =>
    continuous_apply (M, i, j)

theorem nuclear_twoMatrix (hA : Nuclear A) : Nuclear (CStarMatrix (Fin 2) (Fin 2) A) := by
  classical
  intro F ε hε
  let E := twoMatrixEntries F
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp E.continuous.continuousAt ε hε
  let entries := Finset.univ.image (fun p : F × Fin 2 × Fin 2 => p.1.val p.2.1 p.2.2)
  obtain ⟨n, hn, φ, ψ, hφ, hψ, hφn, hψn, happ⟩ := hA entries δ hδ
  let P := starHomContinuousLinear (twoMatrixPack n)
  let Q := starHomContinuousLinear (twoMatrixUnpack n)
  let Φ := P.comp (matrixLinearMap (n := Fin 2) φ)
  let Ψ := (matrixLinearMap (n := Fin 2) ψ).comp Q
  have hP := starHomContinuousLinear_norm_le_one (twoMatrixPack n)
  have hQ := starHomContinuousLinear_norm_le_one (twoMatrixUnpack n)
  have hΦ : CompletelyPositive Φ := completelyPositive_comp _ _
    (matrixLinearMap_completelyPositive φ hφ) (starHomContinuous_completelyPositive _)
  have hΨ : CompletelyPositive Ψ := completelyPositive_comp _ _
    (starHomContinuous_completelyPositive _) (matrixLinearMap_completelyPositive ψ hψ)
  have hΦn : ‖Φ‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hP (matrixLinearMap_norm_le_one φ hφ hφn) (norm_nonneg (matrixLinearMap (n := Fin 2) φ)) zero_le_one).trans_eq (one_mul 1))
  have hΨn : ‖Ψ‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (matrixLinearMap_norm_le_one ψ hψ hψn) hQ (norm_nonneg Q) zero_le_one).trans_eq (one_mul 1))
  have hval (M : CStarMatrix (Fin 2) (Fin 2) A) :
      Ψ (Φ M) = matrixLinearMap ψ (matrixLinearMap φ M) := by
    change matrixLinearMap ψ (twoMatrixUnpack n (twoMatrixPack n (matrixLinearMap φ M))) = _
    rw [twoMatrixUnpack_pack]
  let e (p : F × Fin 2 × Fin 2) := ψ (φ (p.1.val p.2.1 p.2.2)) - p.1.val p.2.1 p.2.2
  have he : ‖e‖ < δ := by
    apply (pi_norm_lt_iff hδ).mpr
    intro p
    exact happ _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
  have heE : ‖E e‖ < ε := by
    have h := hclose (show dist e 0 < δ by simpa only [dist_zero_right] using he)
    simpa only [map_zero, dist_zero_right] using h
  refine ⟨2 * n, by omega, Φ, Ψ, hΦ, hΨ, hΦn, hΨn, ?_⟩
  intro M hM
  have h := (norm_le_pi_norm (E e) (⟨M, hM⟩ : F)).trans_lt heE
  rw [hval]
  exact h

end WeakPureInfiniteness

end

end OAI
