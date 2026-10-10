import OAI.Analysis.KadisonKastler.TracialMatrixInjectivity
import OAI.Analysis.KadisonKastler.OriginalIrreducibleSubfactor

namespace OAI

/-! # Transporting finite matrix retractions through an ambient extension

Only the finite matrix images are inverted. The ambient map is required to
agree with the represented algebra and to be contractive; no continuity in
the weak operator topology is assumed for it.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable (E : MatrixUnitSystem ι (Algebra M)) (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)

omit [Nonempty ι] in
/-- Membership in a finite matrix image is preserved by the given algebra isomorphism. -/
theorem mem_mapped_matrix_concrete (a : Algebra M) :
    (e a).val ∈ (E.map e.toStarAlgHom).concreteAlgebra ↔ a.val ∈ E.concreteAlgebra := by
  rw [(E.map e.toStarAlgHom).mem_concreteAlgebra, E.mem_concreteAlgebra]
  constructor
  · rintro ⟨m,hm⟩
    refine ⟨m, e.injective ?_⟩
    change e (E.hom m) = e a
    exact (mapped_matrixUnits_hom E e.toStarAlgHom m).symm.trans hm
  · rintro ⟨m,hm⟩
    refine ⟨m,?_⟩
    change (E.map e.toStarAlgHom).hom m = e a
    exact (mapped_matrixUnits_hom E e.toStarAlgHom m).trans (congrArg e hm)

/-- The given isomorphism restricted to the concrete finite matrix images. -/
def matrixTransferEquiv :
    Algebra (matrixUnitConcreteAlgebra E) ≃⋆ₐ[ℂ]
      Algebra (matrixUnitConcreteAlgebra (E.map e.toStarAlgHom)) where
  toFun a := ⟨(e (coordinateInclusion (matrixUnitConcreteAlgebra_le E) a)).val,
    (mem_mapped_matrix_concrete E e _).mpr a.property⟩
  invFun b := ⟨(e.symm (coordinateInclusion
      (matrixUnitConcreteAlgebra_le (E.map e.toStarAlgHom)) b)).val, by
    apply (mem_mapped_matrix_concrete E e _).mp
    rw [e.apply_symm_apply]
    exact b.property⟩
  left_inv a := by
    apply Subtype.ext
    exact congrArg (fun z : Algebra M => z.val) (e.symm_apply_apply
      (coordinateInclusion (matrixUnitConcreteAlgebra_le E) a))
  right_inv b := by
    apply Subtype.ext
    exact congrArg (fun z : Algebra N => z.val) (e.apply_symm_apply
      (coordinateInclusion (matrixUnitConcreteAlgebra_le (E.map e.toStarAlgHom)) b))
  map_mul' a b := by
    apply Subtype.ext
    exact congrArg (fun z : Algebra N => z.val)
      (map_mul e (coordinateInclusion (matrixUnitConcreteAlgebra_le E) a)
        (coordinateInclusion (matrixUnitConcreteAlgebra_le E) b))
  map_add' a b := by
    apply Subtype.ext
    exact congrArg (fun z : Algebra N => z.val)
      (map_add e (coordinateInclusion (matrixUnitConcreteAlgebra_le E) a)
        (coordinateInclusion (matrixUnitConcreteAlgebra_le E) b))
  map_smul' c a := by
    apply Subtype.ext
    exact congrArg (fun z : Algebra N => z.val)
      (map_smul e c (coordinateInclusion (matrixUnitConcreteAlgebra_le E) a))
  map_star' a := by
    apply Subtype.ext
    exact congrArg (fun z : Algebra N => z.val)
      (map_star e (coordinateInclusion (matrixUnitConcreteAlgebra_le E) a))

omit [Nonempty ι] in
@[simp] theorem matrixTransferEquiv_inclusion
    (b : Algebra (matrixUnitConcreteAlgebra (E.map e.toStarAlgHom))) :
    e (coordinateInclusion (matrixUnitConcreteAlgebra_le E)
      ((matrixTransferEquiv E e).symm b)) =
      coordinateInclusion (matrixUnitConcreteAlgebra_le (E.map e.toStarAlgHom)) b :=
  e.apply_symm_apply _

variable [Nontrivial K]
  (τ : TracialRepresentation N)
  (R : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K))
  (hR : ∀ T, ‖R T‖ ≤ ‖T‖)

/-- A finite-stage retraction on the original ambient operators. -/
def transferredMatrixRetraction (o : ι) :
    (H →L[ℂ] H) →L[ℂ] Algebra (matrixUnitConcreteAlgebra E) := by
  let L := (matrixTransferEquiv E e).symm.toAlgEquiv.toLinearMap.comp
    ((matrixTraceRetraction τ (E.map e.toStarAlgHom) o).toLinearMap.comp R)
  have hL (T : H →L[ℂ] H) : ‖L T‖ ≤ ‖T‖ := by
    change ‖(matrixTransferEquiv E e).symm
      (matrixTraceRetraction τ (E.map e.toStarAlgHom) o (R T))‖ ≤ ‖T‖
    have he (b) : ‖(matrixTransferEquiv E e).symm b‖ = ‖b‖ :=
      NonUnitalStarAlgHom.norm_map (matrixTransferEquiv E e).symm.toStarAlgHom
        (matrixTransferEquiv E e).symm.injective b
    rw [he]
    have hb := (matrixTraceRetraction τ (E.map e.toStarAlgHom) o).le_of_opNorm_le
      (matrixTraceRetraction_norm τ (E.map e.toStarAlgHom) o) (R T)
    rw [one_mul] at hb
    exact hb.trans (hR T)
  exact L.mkContinuous 1 (fun T => by simpa only [one_mul] using hL T)

theorem transferredMatrixRetraction_norm (o : ι) :
    ‖transferredMatrixRetraction E e τ R hR o‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  change ‖(matrixTransferEquiv E e).symm
    (matrixTraceRetraction τ (E.map e.toStarAlgHom) o (R T))‖ ≤ 1 * ‖T‖
  have he (b) : ‖(matrixTransferEquiv E e).symm b‖ = ‖b‖ :=
    NonUnitalStarAlgHom.norm_map (matrixTransferEquiv E e).symm.toStarAlgHom
      (matrixTransferEquiv E e).symm.injective b
  rw [one_mul, he]
  have hb := (matrixTraceRetraction τ (E.map e.toStarAlgHom) o).le_of_opNorm_le
    (matrixTraceRetraction_norm τ (E.map e.toStarAlgHom) o) (R T)
  rw [one_mul] at hb
  exact hb.trans (hR T)

/-- On the original algebra the transported retraction is the trace expectation. -/
theorem transferredMatrixRetraction_expectation (o : ι)
    (hRa : ∀ a : Algebra M, R a.val = (e a).val) (a : Algebra M) :
    e (coordinateInclusion (matrixUnitConcreteAlgebra_le E)
      (transferredMatrixRetraction E e τ R hR o a.val)) =
    conditionalExpectation τ (matrixUnitConcreteAlgebra_le (E.map e.toStarAlgHom)) (e a) := by
  change e (coordinateInclusion (matrixUnitConcreteAlgebra_le E)
    ((matrixTransferEquiv E e).symm
      (matrixTraceRetraction τ (E.map e.toStarAlgHom) o (R a.val)))) = _
  rw [matrixTransferEquiv_inclusion, hRa]
  exact (matrixTraceRetraction_eq_expectation τ (E.map e.toStarAlgHom) o (e a)).symm

end

end KadisonKastler

end OAI
