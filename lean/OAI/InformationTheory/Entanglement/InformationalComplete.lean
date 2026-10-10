import OAI.InformationTheory.Entanglement.EveBlocks

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [Fintype n] [DecidableEq n] in
lemma projector_polarization (x y : n → ℂ) :
    projector (x+y)-projector x-projector y+
      Complex.I • (projector (x+Complex.I • y)-projector x-projector y)=
    (2 : ℂ) • Matrix.vecMulVec x (star y) := by
  ext i j
  simp only [projector,Matrix.vecMulVec_apply,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,Pi.add_apply,Pi.smul_apply,Pi.star_apply,smul_eq_mul,
    star_add,star_mul,Complex.star_def,Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq,Complex.I_pow_three]
  ring

def testBasis (i : n) : n → ℂ := Pi.single i 1
omit [Fintype n] in
lemma star_testBasis (i : n) : star (testBasis i)=testBasis i := by
  ext j
  simp [testBasis,Pi.single_apply]
omit [Fintype n] in
lemma single_projector_polarization (i j : n) :
    (2 : ℂ) • Matrix.single i j 1=
      projector (testBasis i+testBasis j)-projector (testBasis i)-projector (testBasis j)+
      Complex.I • (projector (testBasis i+Complex.I • testBasis j)-
        projector (testBasis i)-projector (testBasis j)) := by
  rw [projector_polarization,star_testBasis]
  congr 1
  exact Matrix.single_eq_single_vecMulVec_single i j

theorem linear_eq_zero_of_projector_tests (L : Mat n →ₗ[ℂ] ℂ)
    (hbase : ∀ i, L (projector (testBasis i))=0)
    (hplus : ∀ i j, L (projector (testBasis i+testBasis j))=0)
    (himag : ∀ i j, L (projector (testBasis i+Complex.I • testBasis j))=0) :
    L=0 := by
  have hs (i j : n) : L (Matrix.single i j 1)=0 := by
    have h := congrArg L (single_projector_polarization i j)
    simp only [map_smul,map_add,map_sub,hbase,hplus,himag,sub_zero,zero_add,smul_zero] at h
    simpa using h
  ext A
  induction A using Matrix.induction_on' with
  | h_zero => exact map_zero L
  | h_add A B hA hB => simp [hA,hB]
  | h_std_basis i j c =>
    have he : Matrix.single i j c=c • Matrix.single i j (1 : ℂ) := by simp
    rw [he,map_smul,hs,smul_zero]
    rfl

abbrev PositiveTestIndex (n : Type) := n ⊕ ((n×n) ⊕ (n×n))
def positiveTestVector : PositiveTestIndex n → n → ℂ
  | .inl i => testBasis i
  | .inr (.inl (i,j)) => testBasis i+testBasis j
  | .inr (.inr (i,j)) => testBasis i+Complex.I • testBasis j
def positiveTest (k : PositiveTestIndex n) : Mat n := projector (positiveTestVector k)
lemma positiveTest_psd (k : PositiveTestIndex n) : (positiveTest k).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _
lemma linear_eq_zero_of_positive_tests (L : Mat n →ₗ[ℂ] ℂ)
    (h : ∀ k, L (positiveTest k)=0) : L=0 := by
  apply linear_eq_zero_of_projector_tests L
  · exact fun i => h (.inl i)
  · exact fun i j => h (.inr (.inl (i,j)))
  · exact fun i j => h (.inr (.inr (i,j)))

def tensorTraceDifference (W : Mat (n×m)) (X : Mat n) (Y : Mat m) :
    Mat n →ₗ[ℂ] Mat m →ₗ[ℂ] ℂ where
  toFun E :=
    { toFun := fun G => Matrix.trace ((E ⊗ₖ G)*W)-Matrix.trace (E*X)*Matrix.trace (G*Y)
      map_add' := by
        intro G H
        simp only [Matrix.kronecker_add,Matrix.add_mul,Matrix.trace_add]
        ring
      map_smul' := by
        intro c G
        simp only [Matrix.kronecker_smul,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,RingHom.id_apply]
        ring }
  map_add' := by
    intro E G
    ext H
    change Matrix.trace (((E+G) ⊗ₖ H)*W)-Matrix.trace ((E+G)*X)*Matrix.trace (H*Y)=
      (Matrix.trace ((E ⊗ₖ H)*W)-Matrix.trace (E*X)*Matrix.trace (H*Y))+
        (Matrix.trace ((G ⊗ₖ H)*W)-Matrix.trace (G*X)*Matrix.trace (H*Y))
    simp only [Matrix.add_kronecker,Matrix.add_mul,Matrix.trace_add]
    ring
  map_smul' := by
    intro c E
    ext G
    change Matrix.trace (((c • E) ⊗ₖ G)*W)-Matrix.trace ((c • E)*X)*Matrix.trace (G*Y)=
      c • (Matrix.trace ((E ⊗ₖ G)*W)-Matrix.trace (E*X)*Matrix.trace (G*Y))
    simp only [Matrix.smul_kronecker,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul]
    ring

theorem tensor_product_of_positive_tests (W : Mat (n×m)) (X : Mat n) (Y : Mat m)
    (htest : ∀ e : PositiveTestIndex n, ∀ g : PositiveTestIndex m,
      Matrix.trace ((positiveTest e ⊗ₖ positiveTest g)*W)=
        Matrix.trace (positiveTest e*X)*Matrix.trace (positiveTest g*Y)) :
    W=X ⊗ₖ Y := by
  let L := tensorTraceDifference W X Y
  have hL (g : PositiveTestIndex m) : ∀ E, L E (positiveTest g)=0 := by
    have hz := linear_eq_zero_of_positive_tests (L.flip (positiveTest g))
      (fun e => sub_eq_zero.mpr (htest e g))
    intro E
    exact LinearMap.congr_fun hz E
  have hz (E : Mat n) : L E=0 :=
    linear_eq_zero_of_positive_tests (L E) (fun g => hL g E)
  ext ⟨i,a⟩ ⟨j,b⟩
  have h := LinearMap.congr_fun (hz (Matrix.single j i 1)) (Matrix.single b a 1)
  change Matrix.trace (((Matrix.single j i (1 : ℂ)) ⊗ₖ Matrix.single b a 1)*W)-
    Matrix.trace (Matrix.single j i 1*X)*Matrix.trace (Matrix.single b a 1*Y)=0 at h
  simpa only [Matrix.single_kronecker_single,one_mul,Matrix.trace_single_mul,one_smul,
    sub_eq_zero,Matrix.kronecker_apply] using h

end SecretKey

end

end OAI
