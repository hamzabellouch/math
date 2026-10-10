import OAI.Analysis.KadisonKastler.MatrixCorrection
import OAI.Analysis.KadisonKastler.Haagerup
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! # Scalar and limit consequences of complete bounds -/

namespace KadisonKastler

noncomputable section

open Filter Topology

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The one-by-one matrix copy of the algebra. -/
def scalarMatrixCopy : A →⋆ₐ[ℂ] CStarMatrix (Fin 1) (Fin 1) A where
  toFun a := CStarMatrix.ofMatrix fun _ _ => a
  map_one' := by ext i j; fin_cases i; fin_cases j; rfl
  map_mul' a b := by
    ext i j
    change a * b = ∑ _ : Fin 1, a * b
    simp
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by ext i j; fin_cases i; fin_cases j; rfl
  map_star' _ := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem scalarMatrixCopy_apply (a : A) (i j : Fin 1) :
    scalarMatrixCopy a i j = a := rfl

@[simp] theorem scalarMatrixCopy_norm (a : A) : ‖scalarMatrixCopy a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map scalarMatrixCopy
    (fun _ _ h => congrArg (fun X : CStarMatrix (Fin 1) (Fin 1) A => X 0 0) h) a

/-- A complete bound includes the ordinary operator bound with no loss. -/
theorem CompletelyBoundedBy.apply_norm_le {D : A →ₗ[ℂ] B} {c : ℝ}
    (hD : CompletelyBoundedBy D c) (x : A) : ‖D x‖ ≤ c * ‖x‖ := by
  have h := hD 1 1 (scalarMatrixCopy x)
  have he : CStarMatrix.mapₗ D (scalarMatrixCopy x) = scalarMatrixCopy (D x) := by
    ext i j
    rfl
  simpa only [he, scalarMatrixCopy_norm] using h

/-- The row-column bound includes the scalar bilinear bound. -/
theorem HaagerupBound.apply_norm_le {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) (x y : A) : ‖f x y‖ ≤ c * ‖x‖ * ‖y‖ := by
  have h := hf 1 1 1 (scalarMatrixCopy x) (scalarMatrixCopy y)
  have he : bilinearProduct f (scalarMatrixCopy x) (scalarMatrixCopy y) =
      scalarMatrixCopy (f x y) := by
    ext i j
    simp only [bilinearProduct_apply, scalarMatrixCopy_apply, Fin.sum_univ_one]
  simpa only [he, scalarMatrixCopy_norm] using h

/-- Turn a completely bounded algebraic map into a continuous linear map. -/
def CompletelyBoundedBy.toContinuousLinearMap {D : A →ₗ[ℂ] B} {c : ℝ}
    (hD : CompletelyBoundedBy D c) : A →L[ℂ] B :=
  D.mkContinuous c hD.apply_norm_le

@[simp] theorem CompletelyBoundedBy.toContinuousLinearMap_apply
    {D : A →ₗ[ℂ] B} {c : ℝ} (hD : CompletelyBoundedBy D c) (x : A) :
    hD.toContinuousLinearMap x = D x := rfl

/-- A sufficiently small completely bounded perturbation of the identity is
an algebraic linear equivalence, before any multiplicativity is considered. -/
theorem CompletelyBoundedBy.exists_equiv_add_id {D : A →ₗ[ℂ] A} {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) (hD : CompletelyBoundedBy D c) :
    ∃ L : A ≃ₗ[ℂ] A, L.toLinearMap = LinearMap.id + D := by
  let T := hD.toContinuousLinearMap
  have hT : ‖T‖ < 1 :=
    (ContinuousLinearMap.opNorm_le_bound _ hc hD.apply_norm_le).trans_lt hc1
  have hunit : IsUnit (1 + T) := by
    have h := isUnit_one_sub_of_norm_lt_one (x := -T) (by simpa using hT)
    simpa only [sub_neg_eq_add] using h
  obtain ⟨U, hU⟩ := hunit
  refine ⟨(ContinuousLinearEquiv.unitsEquiv ℂ A U).toLinearEquiv, ?_⟩
  ext x
  change (U : A →L[ℂ] A) x = x + D x
  rw [hU]
  rfl

/-- Complete bounds are closed under pointwise limits. This suffices to pass
uniform rectangular estimates to the norm limit of correction maps. -/
theorem completelyBoundedBy_of_pointwise_tendsto {ι : Type*} {l : Filter ι}
    [l.NeBot] (F : ι → A →ₗ[ℂ] B) (G : A →ₗ[ℂ] B) {c : ℝ}
    (hF : ∀ i, CompletelyBoundedBy (F i) c)
    (hG : ∀ x, Tendsto (fun i => F i x) l (𝓝 (G x))) :
    CompletelyBoundedBy G c := by
  intro p q X
  have ht : Tendsto (fun i => CStarMatrix.mapₗ (F i) X) l
      (𝓝 (CStarMatrix.mapₗ G X)) := by
    apply CStarMatrix.ofMatrixL.continuous.tendsto _ |>.comp
    exact tendsto_pi_nhds.mpr fun j => tendsto_pi_nhds.mpr fun k => hG (X j k)
  exact le_of_tendsto ht.norm (Filter.Eventually.of_forall fun i => hF i p q X)

end

end KadisonKastler

end OAI
