import OAI.Analysis.OperatorAlgebra.FiniteHilbertCompression
import OAI.Analysis.OInfinity.FiniteWords

namespace OAI

/-! # Finite Fock-space compression of the canonical O∞ model -/

noncomputable section
open scoped CStarAlgebra ComplexOrder InnerProductSpace ENNReal

namespace WeakPureInfiniteness

abbrev FiniteFockIndex (N m : ℕ) := Σ k : Fin (m + 1), Fin k.val → Fin N

def finiteFockWord {N m : ℕ} (i : FiniteFockIndex N m) : List ℕ :=
  List.ofFn (fun j => (i.2 j : ℕ))

lemma finiteFockWord_injective (N m : ℕ) :
    Function.Injective (@finiteFockWord N m) := by
  rintro ⟨k, v⟩ ⟨l, w⟩ h
  have hlen : k.val = l.val := by
    have hh := congrArg List.length h
    simpa only [finiteFockWord, List.length_ofFn] using hh
  have hkl : k = l := Fin.ext hlen
  subst l
  have hfun : (fun j => (v j : ℕ)) = (fun j => (w j : ℕ)) :=
    List.ofFn_injective h
  have hvw : v = w := by
    funext j
    exact Fin.ext (congrFun hfun j)
  subst w
  rfl

def finiteFockVector {N m : ℕ} (i : FiniteFockIndex N m) : FockSpace :=
  lp.single 2 (finiteFockWord i) 1

lemma finiteFockVector_orthonormal (N m : ℕ) :
    Orthonormal ℂ (@finiteFockVector N m) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [finiteFockVector, lp.inner_single_left, lp.single_apply]
  by_cases h : i = j
  · subst j; simp
  · have hword : finiteFockWord i ≠ finiteFockWord j :=
      fun he => h (finiteFockWord_injective N m he)
    simp [h, hword]

def finiteFockLinear (N m : ℕ) : EuclideanSpace ℂ (FiniteFockIndex N m) →ₗ[ℂ] FockSpace where
  toFun x := ∑ i, (x i) • finiteFockVector i
  map_add' x y := by simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

lemma finiteFockLinear_basis (N m : ℕ) (i : FiniteFockIndex N m) :
    finiteFockLinear N m (EuclideanSpace.basisFun (FiniteFockIndex N m) ℂ i) =
      finiteFockVector i := by
  classical
  simp [finiteFockLinear, EuclideanSpace.basisFun_apply, PiLp.single_apply]

def finiteFockIsometry (N m : ℕ) : EuclideanSpace ℂ (FiniteFockIndex N m) →ₗᵢ[ℂ] FockSpace := by
  let b := EuclideanSpace.basisFun (FiniteFockIndex N m) ℂ
  have hv : Orthonormal ℂ ((finiteFockLinear N m) ∘ b) := by
    have he : (finiteFockLinear N m) ∘ b = @finiteFockVector N m := by
      funext i
      exact finiteFockLinear_basis N m i
    rw [he]
    exact finiteFockVector_orthonormal N m
  exact (finiteFockLinear N m).isometryOfOrthonormal (v := b.toBasis) b.orthonormal hv

def scalarMatrixOperatorEquiv (n : Type*) [Fintype n] [DecidableEq n] :
    CStarMatrix n n ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  CStarMatrix.ofMatrixStarAlgEquiv.symm.trans Matrix.toEuclideanCLM

lemma scalarMatrixOperatorEquiv_basis (n : Type*) [Fintype n] [DecidableEq n]
    (M : CStarMatrix n n ℂ) (i j : n) :
    scalarMatrixOperatorEquiv n M (EuclideanSpace.basisFun n ℂ j) i = M i j := by
  simpa [scalarMatrixOperatorEquiv, EuclideanSpace.basisFun_apply,
    Matrix.mulVec, dotProduct, PiLp.single_apply] using
      (show CStarMatrix.ofMatrixStarAlgEquiv.symm M i j = M i j from rfl)

lemma scalarMatrixOperatorEquiv_symm_apply (n : Type*) [Fintype n] [DecidableEq n]
    (T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (i j : n) :
    (scalarMatrixOperatorEquiv n).symm T i j =
      inner ℂ (EuclideanSpace.basisFun n ℂ i) (T (EuclideanSpace.basisFun n ℂ j)) := by
  rw [← scalarMatrixOperatorEquiv_basis n ((scalarMatrixOperatorEquiv n).symm T) i j,
    StarAlgEquiv.apply_symm_apply]
  exact (EuclideanSpace.basisFun_inner (𝕜 := ℂ) n _ i).symm

def fockOperatorRepresentation : OInfinity →⋆ₐ[ℂ] (FockSpace →L[ℂ] FockSpace) :=
  oInfinityEvaluation fockRepresentation

def oInfinityFockOperatorCompression (N m : ℕ) :
    OInfinity →L[ℂ] (EuclideanSpace ℂ (FiniteFockIndex N m) →L[ℂ]
      EuclideanSpace ℂ (FiniteFockIndex N m)) :=
  hilbertCompression fockOperatorRepresentation.toNonUnitalStarAlgHom
    (finiteFockIsometry N m).toContinuousLinearMap

def oInfinityFockCompression (N m : ℕ) :
    OInfinity →L[ℂ] CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) ℂ :=
  (starHomContinuousLinear
    (scalarMatrixOperatorEquiv (FiniteFockIndex N m)).symm.toStarAlgHom.toNonUnitalStarAlgHom).comp
      (oInfinityFockOperatorCompression N m)

local instance : PartialOrder OInfinity := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing OInfinity := CStarAlgebra.spectralOrderedRing _

lemma oInfinityFockOperatorCompression_cp (N m : ℕ) :
    CompletelyPositive (oInfinityFockOperatorCompression N m) :=
  hilbertCompression_cp _ _

lemma oInfinityFockOperatorCompression_norm_le (N m : ℕ) :
    ‖oInfinityFockOperatorCompression N m‖ ≤ 1 := by
  exact (hilbertCompression_norm_le _ _).trans
    ((mul_le_mul (finiteFockIsometry N m).norm_toContinuousLinearMap_le
      (finiteFockIsometry N m).norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one).trans
        (by norm_num))

lemma oInfinityFockCompression_cp (N m : ℕ) :
    CompletelyPositive (oInfinityFockCompression N m) := by
  intro n X hX
  have h := oInfinityFockOperatorCompression_cp N m n X hX
  exact map_nonneg (CStarMatrix.mapₙₐ
    (scalarMatrixOperatorEquiv (FiniteFockIndex N m)).symm.toStarAlgHom.toNonUnitalStarAlgHom) h

lemma oInfinityFockCompression_norm_le (N m : ℕ) :
    ‖oInfinityFockCompression N m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  change ‖(scalarMatrixOperatorEquiv (FiniteFockIndex N m)).symm
    (oInfinityFockOperatorCompression N m a)‖ ≤ _
  calc
    _ ≤ ‖oInfinityFockOperatorCompression N m a‖ :=
      NonUnitalStarAlgHom.norm_apply_le
        (scalarMatrixOperatorEquiv (FiniteFockIndex N m)).symm.toStarAlgHom.toNonUnitalStarAlgHom _
    _ ≤ ‖oInfinityFockOperatorCompression N m‖ * ‖a‖ :=
      (oInfinityFockOperatorCompression N m).le_opNorm a
    _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right
      (oInfinityFockOperatorCompression_norm_le N m) (norm_nonneg _)

@[simp] lemma finiteFockIsometry_basis (N m : ℕ) (i : FiniteFockIndex N m) :
    finiteFockIsometry N m (EuclideanSpace.basisFun (FiniteFockIndex N m) ℂ i) =
      finiteFockVector i := finiteFockLinear_basis N m i

lemma oInfinityFockCompression_apply (N m : ℕ) (a : OInfinity)
    (i j : FiniteFockIndex N m) :
    oInfinityFockCompression N m a i j = inner ℂ (finiteFockVector i)
      (fockOperatorRepresentation a (finiteFockVector j)) := by
  change (scalarMatrixOperatorEquiv (FiniteFockIndex N m)).symm
    (oInfinityFockOperatorCompression N m a) i j = _
  rw [scalarMatrixOperatorEquiv_symm_apply]
  change inner ℂ _ ((finiteFockIsometry N m).toContinuousLinearMap.adjoint
    ((fockOperatorRepresentation a)
      (finiteFockIsometry N m (EuclideanSpace.basisFun (FiniteFockIndex N m) ℂ j)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (finiteFockIsometry N m (EuclideanSpace.basisFun (FiniteFockIndex N m) ℂ i))
    ((fockOperatorRepresentation a)
      (finiteFockIsometry N m (EuclideanSpace.basisFun (FiniteFockIndex N m) ℂ j))) = _
  rw [finiteFockIsometry_basis, finiteFockIsometry_basis]

lemma oInfinityFockCompression_one (N m : ℕ) :
    oInfinityFockCompression N m 1 = 1 := by
  have hV := (ContinuousLinearMap.isometry_iff_adjoint_comp_self
    (finiteFockIsometry N m).toContinuousLinearMap).mp (finiteFockIsometry N m).isometry
  have h : oInfinityFockOperatorCompression N m 1 = 1 := by
    change (finiteFockIsometry N m).toContinuousLinearMap.adjoint.comp
      ((fockOperatorRepresentation.toNonUnitalStarAlgHom 1).comp
        (finiteFockIsometry N m).toContinuousLinearMap) = 1
    rw [StarAlgHom.coe_toNonUnitalStarAlgHom, map_one]
    change (finiteFockIsometry N m).toContinuousLinearMap.adjoint.comp
      (finiteFockIsometry N m).toContinuousLinearMap = 1
    exact hV
  change (scalarMatrixOperatorEquiv (FiniteFockIndex N m)).symm
    (oInfinityFockOperatorCompression N m 1) = 1
  rw [h, map_one]

end WeakPureInfiniteness

end

end OAI
