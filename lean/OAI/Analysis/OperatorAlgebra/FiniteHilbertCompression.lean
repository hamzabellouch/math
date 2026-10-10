import OAI.Analysis.WeakInfiniteness.MatrixRepresentation
import OAI.Analysis.WeakInfiniteness.CentralState

namespace OAI

/-! # Completely positive compression to a finite Hilbert space

This is the compression used for the finite Fock-space approximations.
-/

noncomputable section
open scoped CStarAlgebra ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

section Amplification

variable {E H n : Type*} [Fintype n]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def amplifyHilbertMap (V : E →L[ℂ] H) :
    PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i => V.comp (ContinuousLinearMap.proj i)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => E)).toContinuousLinearMap)

omit [Fintype n] [CompleteSpace E] [CompleteSpace H] in
@[simp] lemma amplifyHilbertMap_apply (V : E →L[ℂ] H)
    (x : PiLp 2 (fun _ : n => E)) (i : n) :
    amplifyHilbertMap V x i = V (x i) := by simp [amplifyHilbertMap]

lemma amplifyHilbertMap_adjoint (V : E →L[ℂ] H) :
    amplifyHilbertMap (n := n) V.adjoint = (amplifyHilbertMap (n := n) V).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, amplifyHilbertMap_apply,
    ContinuousLinearMap.adjoint_inner_left]

end Amplification

section Compression

variable {A E H : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertCompressionLinear (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (V : E →L[ℂ] H) :
    A →ₗ[ℂ] (E →L[ℂ] E) where
  toFun a := V.adjoint.comp ((π a).comp V)
  map_add' a b := by ext x; simp
  map_smul' c a := by ext x; simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma hilbertCompressionLinear_bound (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (V : E →L[ℂ] H) (a : A) :
    ‖hilbertCompressionLinear π V a‖ ≤ (‖V‖ * ‖V‖) * ‖a‖ := by
  calc
    _ ≤ ‖V.adjoint‖ * (‖π a‖ * ‖V‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖V‖ * (‖a‖ * ‖V‖) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = _ := by ring

def hilbertCompression (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (V : E →L[ℂ] H) :
    A →L[ℂ] (E →L[ℂ] E) :=
  (hilbertCompressionLinear π V).mkContinuous (‖V‖ * ‖V‖)
    (hilbertCompressionLinear_bound π V)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma hilbertCompression_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (V : E →L[ℂ] H) (a : A) :
    hilbertCompression π V a = V.adjoint.comp ((π a).comp V) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma hilbertCompression_norm_le (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (V : E →L[ℂ] H) : ‖hilbertCompression π V‖ ≤ ‖V‖ * ‖V‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (hilbertCompressionLinear_bound π V)

lemma hilbertCompression_cp (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (V : E →L[ℂ] H) :
    CompletelyPositive (hilbertCompression π V) := by
  intro n X hX
  let Y : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E) :=
    CStarMatrix.ofMatrix (fun i j => hilbertCompression π V (X i j))
  let Z := CStarMatrix.mapₙₐ π X
  have hZ : 0 ≤ matrixOperator Z := by
    change 0 ≤ matrixOperatorHom (n := Fin n) (H := H) Z
    exact map_nonneg (matrixOperatorHom (n := Fin n) (H := H))
      (map_nonneg (CStarMatrix.mapₙₐ π) hX)
  have he : matrixOperator Y = (amplifyHilbertMap (n := Fin n) V).adjoint.comp
      ((matrixOperator Z).comp (amplifyHilbertMap V)) := by
    rw [← amplifyHilbertMap_adjoint]
    ext x i
    simp only [matrixOperator_apply, ContinuousLinearMap.comp_apply,
      amplifyHilbertMap_apply, map_sum]
    rfl
  have hY : 0 ≤ matrixOperator Y := by
    rw [he, ContinuousLinearMap.nonneg_iff_isPositive]
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hZ).adjoint_conj
      (amplifyHilbertMap (n := Fin n) V)
  have hreflect := (NonUnitalStarAlgHom.map_le_map_iff
    (matrixOperatorHom (n := Fin n) (H := E)) matrixOperator_injective
    (x := 0) (y := Y)).mp
  apply hreflect
  rw [map_zero]
  change 0 ≤ matrixOperator Y
  exact hY

end Compression

end WeakPureInfiniteness

end

end OAI
