import OAI.Geometry.QuadricBundles.SymmetricFlags

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix
open scoped BigOperators
noncomputable section

structure PolynomialGeneration (n : ℕ) (ι : Type u1) [Fintype ι] where
  coefficient : StandardChart → Fin (n+1) → ι → BasePolynomial
  recovery : StandardChart → Fin (n+1) → ι → BasePolynomial
  leftInverse : ∀ i z (w : Fin (n+1) → ℂ),
    Matrix.mulVec (fun a q ↦ baseEval (recovery i a q) z)
      (Matrix.mulVec (Matrix.transpose (fun a q ↦ baseEval (coefficient i a q) z)) w)=w
namespace PolynomialGeneration
variable {n : ℕ} {ι : Type u2} [Fintype ι] (B : PolynomialGeneration n ι)
def matrix (i : StandardChart) (z : BaseCoordinates) : Matrix (Fin (n+1)) ι ℂ :=
  fun a q ↦ baseEval (B.coefficient i a q) z
def recover (i : StandardChart) (z : BaseCoordinates) : Matrix (Fin (n+1)) ι ℂ :=
  fun a q ↦ baseEval (B.recovery i a q) z
lemma recover_matrix (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) :
    (B.recover i z).mulVec ((B.matrix i z).transpose.mulVec w)=w := B.leftInverse i z w
lemma matrix_injective (i : StandardChart) (z : BaseCoordinates) :
    Function.Injective ((B.matrix i z).transpose.mulVec) := by
  intro w w' h
  have he := congrArg (B.recover i z).mulVec h
  simpa only [B.recover_matrix] using he
lemma matrix_nonzero (i : StandardChart) (z : BaseCoordinates) {w : Fin (n+1) → ℂ} (hw : w≠0) :
    (B.matrix i z).transpose.mulVec w≠0 := by
  intro hh
  apply hw
  apply B.matrix_injective i z
  simpa only [mulVec_zero] using hh
end PolynomialGeneration
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix BinaryForms LaurentCech
open scoped BigOperators
noncomputable section

namespace EqualizerData
variable (D : EqualizerData) (m e t : ℕ) (he : 3*m≤e)
abbrev SymmetricGeneratorIndex := StandardChart × Fin (2*t+1)
def symmetricGeneratorValue (i : StandardChart) (z : BaseCoordinates) :
    Matrix (Fin (2*t+1)) (SymmetricGeneratorIndex t) ℂ :=
  fun a q ↦ ((D.flagBasis m t i z).mulVec
    (TriangularCechBundle.polynomialValue ((D.symmetricFlag m e t he).generator q.1 q.2).polynomial i z)) a
lemma symmetricGeneratorValue_regular (i : StandardChart) (a : Fin (2*t+1))
    (q : SymmetricGeneratorIndex t) :
    UniformlyRegularOn univ (fun z ↦ D.symmetricGeneratorValue m e t he i z a q) := by
  change UniformlyRegularOn univ (fun z ↦ ∑ b, D.flagBasis m t i z a b *
    baseEval (((D.symmetricFlag m e t he).generator q.1 q.2).polynomial i b) z)
  apply UniformlyRegularOn.fintype_sum
  intro b
  exact (D.flagBasis_regular m t i a b).mul (uniformlyRegular_polynomial univ _)

def localGeneratorMatrix (i : StandardChart) (z : BaseCoordinates) :
    Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  fun a b ↦ D.symmetricGeneratorValue m e t he i z a (i,b)
lemma localGeneratorMatrix_det_unit (i : StandardChart) (z : BaseCoordinates) :
    IsUnit (D.localGeneratorMatrix m e t he i z).det := by
  let B := D.symmetricFlag m e t he
  let Q : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ := fun a b ↦
    baseEval ((B.generator i b).polynomial i a) z
  have hQ : Q.det=1 := by
    rw [Matrix.det_of_isUpperTriangular (fun a b hab ↦ by
      dsimp [Q]; rw [B.generator_high i i b a hab]; simp)]
    apply Finset.prod_eq_one
    intro b _
    dsimp [Q]
    rw [B.generator_diagonal]
    simp [lineGenerator]
  have hmat : D.localGeneratorMatrix m e t he i z=D.flagBasis m t i z*Q := rfl
  rw [hmat,Matrix.det_mul,hQ,mul_one]
  exact D.flagBasis_det_unit m t i z
lemma localGeneratorMatrix_regular (i : StandardChart) (a b : Fin (2*t+1)) :
    UniformlyRegularOn univ (fun z ↦ D.localGeneratorMatrix m e t he i z a b) :=
  D.symmetricGeneratorValue_regular m e t he i a (i,b)

def generatorRecoveryValue (i : StandardChart) (z : BaseCoordinates) :
    Matrix (Fin (2*t+1)) (SymmetricGeneratorIndex t) ℂ :=
  fun a q ↦ if q.1=i then ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a q.2 else 0
lemma generatorRecoveryValue_regular (i : StandardChart) (a : Fin (2*t+1))
    (q : SymmetricGeneratorIndex t) :
    UniformlyRegularOn univ (fun z ↦ D.generatorRecoveryValue m e t he i z a q) := by
  by_cases h : q.1=i
  · simp only [generatorRecoveryValue,ite_eq_left h]
    apply UniformlyRegularOn.matrix_inv
    · intro a b
      exact D.localGeneratorMatrix_regular m e t he i b a
    · intro z _
      simpa only [Matrix.det_transpose] using D.localGeneratorMatrix_det_unit m e t he i z
  · simpa only [generatorRecoveryValue,ite_eq_right h] using uniformlyRegular_const univ (0 : ℂ)
lemma generatorRecoveryValue_leftInverse (i : StandardChart) (z : BaseCoordinates)
    (w : Fin (2*t+1) → ℂ) :
    (D.generatorRecoveryValue m e t he i z).mulVec
      ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w)=w := by
  have hh := Matrix.nonsing_inv_mul ((D.localGeneratorMatrix m e t he i z).transpose)
    (by simpa only [Matrix.det_transpose] using D.localGeneratorMatrix_det_unit m e t he i z)
  have hv := congrArg (fun A : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ ↦ A.mulVec w) hh
  rw [← Matrix.mulVec_mulVec,Matrix.one_mulVec] at hv
  calc
    _ = (((D.localGeneratorMatrix m e t he i z).transpose)⁻¹).mulVec
        ((D.localGeneratorMatrix m e t he i z).transpose.mulVec w) := by
      ext a
      change (∑ q : StandardChart × Fin (2*t+1),
        (if q.1=i then ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a q.2 else 0)*
          ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w) q)=_
      rw [Fintype.sum_prod_type]
      simp only [ite_mul,zero_mul]
      have hi (j : StandardChart) :
          (∑ b : Fin (2*t+1),if j=i then
            ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a b*
              ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w) (j,b) else 0)=
          if j=i then ∑ b : Fin (2*t+1),
            ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a b*
              ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w) (j,b) else 0 := by
        split_ifs <;> simp
      simp_rw [hi]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rfl
    _ = w := hv

def symmetricGeneration : PolynomialGeneration (2*t) (SymmetricGeneratorIndex t) where
  coefficient := fun i a q ↦ (D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose
  recovery := fun i a q ↦ (D.generatorRecoveryValue_regular m e t he i a q).exists_polynomial.choose
  leftInverse := by
    intro i z w
    have hQ : (fun a q ↦ baseEval ((D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose) z)=
        D.symmetricGeneratorValue m e t he i z := by
      funext a q
      exact (congrFun (D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose_spec z).symm
    have hR : (fun a q ↦ baseEval ((D.generatorRecoveryValue_regular m e t he i a q).exists_polynomial.choose) z)=
        D.generatorRecoveryValue m e t he i z := by
      funext a q
      exact (congrFun (D.generatorRecoveryValue_regular m e t he i a q).exists_polynomial.choose_spec z).symm
    rw [hQ,hR]
    exact D.generatorRecoveryValue_leftInverse m e t he i z w
lemma symmetricGeneration_matrix (i : StandardChart) (z : BaseCoordinates) :
    (D.symmetricGeneration m e t he).matrix i z=D.symmetricGeneratorValue m e t he i z := by
  funext a q
  exact (congrFun (D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose_spec z).symm
lemma symmetricGeneratorValue_compatible (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) (q : SymmetricGeneratorIndex t) :
    (D.symmetricGeneratorValue m e t he i z).col q=
      lineFactor (e,e) i j z • (symmetricMatrix (2*t) (D.coordinateTransition i j (powerCoordinates m z))).mulVec
        ((D.symmetricGeneratorValue m e t he j (coordinateChange i j z)).col q) := by
  let B := D.symmetricFlag m e t he
  have hc := (B.generator q.1 q.2).compatible i j z hz
  change (D.flagBasis m t i z).mulVec (TriangularCechBundle.polynomialValue (B.generator q.1 q.2).polynomial i z)=_
  rw [← hc]
  change (D.flagBasis m t i z).mulVec ((D.flagMatrix m e t i j z).mulVec _)=_
  rw [flagMatrix,Matrix.smul_mulVec,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc,← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (D.flagBasis_det_unit m t i z),Matrix.one_mul]
  rw [← Matrix.mulVec_mulVec]
  rfl
end EqualizerData
end
end QuadricCounterexample

end

end OAI
