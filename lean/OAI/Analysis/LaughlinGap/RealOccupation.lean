import Mathlib
import OAI.Analysis.LaughlinGap.Averaging
import OAI.Analysis.LaughlinGap.Creation

namespace OAI

/-! Real Occupation. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def complexify : Matrix ι ι ℝ →ₐ[ℝ]
    Module.End ℂ (EuclideanSpace ℂ ι) where
  toFun A := (A.map (algebraMap ℝ ℂ)).toEuclideanLin
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' A B := by
    rw [Matrix.map_mul, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    rfl
  map_zero' := by simp
  map_add' A B := by
    rw [Matrix.map_add _ (map_add (algebraMap ℝ ℂ)), map_add]
  commutes' r := by
    apply LinearMap.ext
    intro x
    ext i
    simp [Algebra.algebraMap_eq_smul_one, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite]

lemma complexify_injective : Function.Injective (complexify (ι := ι)) := by
  intro A B h
  apply_fun Matrix.toEuclideanLin.symm at h
  simp only [complexify, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearEquiv.symm_apply_apply] at h
  ext i j
  exact Complex.ofReal_injective (congrFun (congrFun h i) j)

@[simp] lemma complexify_transpose (A : Matrix ι ι ℝ) :
    complexify A.transpose = (complexify A).adjoint := by
  rw [complexify, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply]

lemma complexify_positive {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (complexify A).IsPositive := by
  rw [complexify, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.isPositive_toEuclideanLin_iff]
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.map_mul]
  have he : (star B).map (algebraMap ℝ ℂ) =
      (B.map (algebraMap ℝ ℂ)).conjTranspose := by
    ext i j
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

abbrev FockMatrix (n : ℕ) := Matrix (Finset (Fin n)) (Finset (Fin n)) ℝ

noncomputable def annihilation {n : ℕ} (j : Fin n) : FockMatrix n := fun A B =>
  if j ∉ A ∧ B = Occupation.flip j A then
    (-1 : ℝ) ^ (A.filter (fun k => k < j)).card else 0

noncomputable def creation {n : ℕ} (j : Fin n) : FockMatrix n :=
  (annihilation j).transpose

@[simp] theorem complexify_annihilation {n : ℕ} (j : Fin n) :
    complexify (annihilation j) = Occupation.annihilation j := by
  apply LinearMap.ext
  intro x
  ext A
  change (∑ B, (annihilation j A B : ℂ) * x B) = _
  by_cases hj : j ∈ A
  · simp [annihilation, Occupation.annihilation, Occupation.transition, hj]
  · simp [annihilation, Occupation.annihilation, Occupation.transition, hj,
      Occupation.sign, apply_ite]

@[simp] theorem complexify_creation {n : ℕ} (j : Fin n) :
    complexify (creation j) = Occupation.creation j := by
  rw [creation, complexify_transpose, complexify_annihilation]
  exact Occupation.annihilation_adjoint j

lemma creation_transpose {n : ℕ} (j : Fin n) : (creation j).transpose = annihilation j :=
  Matrix.transpose_transpose _

lemma annihilation_creation {n : ℕ} (i j : Fin n) :
    annihilation i * creation j + creation j * annihilation i = if i=j then 1 else 0 := by
  apply complexify_injective
  simp only [map_add, map_mul, complexify_annihilation, complexify_creation, apply_ite,
    map_one, map_zero]
  by_cases h : i=j <;> simpa [h, Module.End.one_eq_id, Module.End.mul_eq_comp] using
    Occupation.annihilation_creation_CAR i j

lemma annihilation_anticommute {n : ℕ} (i j : Fin n) :
    annihilation i * annihilation j = -(annihilation j * annihilation i) := by
  apply complexify_injective
  simp only [map_mul, map_neg, complexify_annihilation]
  exact Occupation.annihilation_anticommute i j

lemma creation_anticommute {n : ℕ} (i j : Fin n) :
    creation i * creation j = -(creation j * creation i) := by
  have h := congrArg Matrix.transpose (annihilation_anticommute j i)
  simpa [Matrix.transpose_mul, Matrix.transpose_neg, creation] using h

noncomputable def secondQuantization {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) : FockMatrix n :=
  ∑ i, ∑ j, L i j • (creation i * annihilation j)

lemma secondQuantization_transpose {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) :
    (secondQuantization L).transpose = secondQuantization L.transpose := by
  simp only [secondQuantization, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.transpose_mul, creation, Matrix.transpose_apply, Matrix.transpose_transpose]
  rw [Finset.sum_comm]

lemma elementary_commutator_annihilation {n : ℕ} (i j k : Fin n) :
    (creation i * annihilation j) * annihilation k -
      annihilation k * (creation i * annihilation j) =
        -(if k=i then annihilation j else 0) := by
  have h := annihilation_creation k i
  have h' := annihilation_anticommute j k
  have hm := congrArg (fun B : FockMatrix n => B * annihilation j) h
  simp only [add_mul] at hm
  rw [← mul_assoc] 
  rw [mul_assoc (creation i), h', mul_neg, ← mul_assoc]
  rw [sub_eq_add_neg, ← neg_add, add_comm, hm]
  split_ifs <;> simp

lemma commutator_annihilation {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Averaging.commutator (secondQuantization L) (annihilation k) =
      -∑ j, L k j • annihilation j := by
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk,
    secondQuantization, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, ← Finset.sum_sub_distrib, ← smul_sub,
    elementary_commutator_annihilation, smul_neg, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_ite, smul_zero]
  simp

lemma commutator_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L A B : Matrix ι ι ℝ) :
    Averaging.commutator L (A*B) = Averaging.commutator L A * B + A * Averaging.commutator L B := by
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk]
  noncomm_ring

end LaughlinGap.RealOccupation

end

end OAI
