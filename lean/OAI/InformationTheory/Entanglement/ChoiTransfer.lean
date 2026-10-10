import OAI.InformationTheory.Entanglement.TensorTools

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]
  [DecidableEq n] [DecidableEq m]

omit [Fintype m] [DecidableEq m] in
lemma linearMap_entries (F : Map n m) (X : Mat n) :
    F X = ∑ i, ∑ j, X i j • F (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, ← map_smul]
  simp

def sharp (F : Map n m) : Map m n := transposeMap.comp ((hsAdjoint F).comp transposeMap)

omit [DecidableEq m] in
lemma sharp_apply {F : Map n m} (hF : CP F) (A : Mat m) (i j : n) :
    sharp F A i j = ∑ k, ∑ l, F (Matrix.single i j 1) k l * A k l := by
  change (∑ k, ∑ l, star (F (Matrix.single j i 1) k l)*A l k) = _
  have hentry (k l : m) : star (F (Matrix.single j i 1) k l) =
      F (Matrix.single i j 1) l k := (cp_choi hF).isHermitian.apply (i,l) (j,k)
  simp_rw [hentry]
  rw [Finset.sum_comm]

omit [Fintype m] in
lemma omega_block (i j : m) :
    (Matrix.of fun k l => projector (omega (n := m)) (i,k) (j,l))=Matrix.single i j 1 := by
  ext k l
  simp only [projector,Matrix.vecMulVec_apply,omega,Pi.star_apply,Matrix.single_apply]
  by_cases hik : i=k <;> by_cases hjl : j=l <;> simp [hik,hjl]

lemma choi_transfer {F : Map n m} (hF : CP F) (G : Map m p) :
    choi (G.comp F)=tensorMap (sharp F) G (projector (omega (n := m))) := by
  classical
  ext ⟨i,a⟩ ⟨j,b⟩
  change G (F (Matrix.single i j 1)) a b =
    sharp F (Matrix.of fun k l => G (Matrix.of fun r s => projector (omega (n := m)) (k,r) (l,s)) a b) i j
  simp_rw [omega_block,sharp_apply hF]
  rw [linearMap_entries G]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply]

omit [DecidableEq m] in
lemma tensorMap_smul (a b : ℂ) (F : Map n m) {r s : Type} [Fintype r] [Fintype s]
    (G : Map r s) : tensorMap (a • F) (b • G)=(a*b) • tensorMap F G := by
  classical
  apply linearMap_eq_of_tensors
  intro A B
  simp only [LinearMap.smul_apply,tensorMap_kronecker,Matrix.smul_kronecker,
    Matrix.kronecker_smul,smul_smul,mul_comm]
end SecretKey

end

end OAI
