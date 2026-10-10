import OAI.Analysis.KadisonKastler.FullOperatorMultiplicationCorrection
import OAI.Analysis.KadisonKastler.FaithfulRepresentation

namespace OAI

/-! # Transport of multiplication correction through a star-algebra model -/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def transportBilinear (e : A ≃⋆ₐ[ℂ] B) (m : A →ₗ[ℂ] A →ₗ[ℂ] A) :
    B →ₗ[ℂ] B →ₗ[ℂ] B where
  toFun x := e.toAlgEquiv.toLinearMap.comp
    ((m (e.symm x)).comp e.symm.toAlgEquiv.toLinearMap)
  map_add' x y := by ext z; simp
  map_smul' c x := by ext z; simp

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem transportBilinear_apply (e : A ≃⋆ₐ[ℂ] B)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : B) :
    transportBilinear e m x y = e (m (e.symm x) (e.symm y)) := rfl

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
theorem transportBilinear_assoc (e : A ≃⋆ₐ[ℂ] B)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (hm : ∀ x y z, m (m x y) z = m x (m y z)) :
    ∀ x y z, transportBilinear e m (transportBilinear e m x y) z =
      transportBilinear e m x (transportBilinear e m y z) := by
  intro x y z
  simp only [transportBilinear_apply, e.symm_apply_apply, hm]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
theorem transportBilinear_star (e : A ≃⋆ₐ[ℂ] B)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (hm : ∀ x y, star (m x y) = m (star y) (star x)) :
    ∀ x y, star (transportBilinear e m x y) = transportBilinear e m (star y) (star x) := by
  intro x y
  simp only [transportBilinear_apply, ← map_star, hm]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
theorem bilinearProduct_transport_defect (e : A ≃⋆ₐ[ℂ] B)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) B) (Y : CStarMatrix (Fin r) (Fin q) B) :
    bilinearProduct (transportBilinear e m - LinearMap.mul ℂ B) X Y =
      CStarMatrix.mapₗ e.toAlgEquiv.toLinearMap
        (bilinearProduct (m - LinearMap.mul ℂ A)
          (CStarMatrix.mapₗ e.symm.toAlgEquiv.toLinearMap X)
          (CStarMatrix.mapₗ e.symm.toAlgEquiv.toLinearMap Y)) := by
  ext i j
  simp [map_sum, CStarMatrix.mul_apply]

theorem starAlgEquiv_matrix_norm (e : A ≃⋆ₐ[ℂ] B) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    ‖CStarMatrix.mapₗ e.toAlgEquiv.toLinearMap X‖ = ‖X‖ := by
  exact injective_starAlgHom_completelyIsometric e.toStarAlgHom e.injective p q X

theorem transportBilinear_defect_bound (e : A ≃⋆ₐ[ℂ] B)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) {c : ℝ}
    (hm : HaagerupBound (m - LinearMap.mul ℂ A) c) :
    HaagerupBound (transportBilinear e m - LinearMap.mul ℂ B) c := by
  intro p r q X Y
  rw [bilinearProduct_transport_defect,
    starAlgEquiv_matrix_norm]
  have h := hm p r q (CStarMatrix.mapₗ e.symm.toAlgEquiv.toLinearMap X)
    (CStarMatrix.mapₗ e.symm.toAlgEquiv.toLinearMap Y)
  simpa only [starAlgEquiv_matrix_norm e.symm] using h

/-- An operator-algebra model transfers the constructed correction, without
any dependence on the multiplicity of the original representation. -/
theorem multiplication_correction_of_operator_model
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (e : A ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z))
    (hms : ∀ x y, star (m x y) = m (star y) (star x))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1/11)
    (hb : HaagerupBound (m - LinearMap.mul ℂ A) q) :
    ∃ L : A ≃ₗ[ℂ] A, (∀ x y, L (m x y) = L x * L y) ∧
      (∀ x, L (star x) = star (L x)) ∧
      CompletelyBoundedBy (L.toLinearMap - LinearMap.id) (4 * q) := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  obtain ⟨T, hTm, hTs, hTb⟩ := fullOperator_multiplication_correction
    (transportBilinear e m) (transportBilinear_assoc e m hm)
    (transportBilinear_star e m hms) hq hq1 (transportBilinear_defect_bound e m hb)
  let L := (e.toAlgEquiv.toLinearEquiv.trans T).trans e.symm.toAlgEquiv.toLinearEquiv
  have hL (x : A) : L x = e.symm (T (e x)) := rfl
  refine ⟨L, ?_, ?_, ?_⟩
  · intro x y
    rw [hL, hL, hL, ← map_mul]
    apply congrArg e.symm
    have h := hTm (e x) (e y)
    simpa only [transportBilinear_apply, e.symm_apply_apply] using h
  · intro x
    simp only [hL, map_star, hTs]
  · intro p r X
    have he : CStarMatrix.mapₗ (L.toLinearMap - LinearMap.id) X =
        CStarMatrix.mapₗ e.symm.toAlgEquiv.toLinearMap
          (CStarMatrix.mapₗ (T.toLinearMap - LinearMap.id)
            (CStarMatrix.mapₗ e.toAlgEquiv.toLinearMap X)) := by
      ext i j
      simp [hL]
    rw [he, starAlgEquiv_matrix_norm e.symm]
    have h := hTb p r (CStarMatrix.mapₗ e.toAlgEquiv.toLinearMap X)
    simpa only [starAlgEquiv_matrix_norm e] using h

end

end KadisonKastler

end OAI
