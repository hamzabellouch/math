import OAI.InformationTheory.Entanglement.CPBlocks

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n m p q r s t : Type} [Fintype n] [Fintype m] [Fintype p] [Fintype q]
  [Fintype r] [Fintype s] [Fintype t]

omit [Fintype n] [Fintype m] in
lemma single_product [DecidableEq n] [DecidableEq m] (i j : n × m) :
    (Matrix.single i.1 j.1 (1:ℂ)) ⊗ₖ (Matrix.single i.2 j.2 (1:ℂ)) = Matrix.single i j 1 := by
  simpa using (Matrix.single_kronecker_single i.1 j.1 i.2 j.2 (1:ℂ) 1)

omit [Fintype p] in
lemma linearMap_eq_of_tensors [DecidableEq n] [DecidableEq m]
    (F G : Map (n × m) p)
    (h : ∀ (A : Mat n) (B : Mat m), F (A ⊗ₖ B)=G (A ⊗ₖ B)) : F=G := by
  apply LinearMap.ext
  intro X
  induction X using Matrix.induction_on' with
  | h_zero => simp
  | h_add A B hA hB => simp [hA,hB]
  | h_std_basis i j c =>
    have he : Matrix.single i j c=c • Matrix.single i j (1:ℂ) := by simp
    rw [he,map_smul,map_smul,← single_product]
    rw [h]

lemma tensorMap_comp [DecidableEq n] [DecidableEq m]
    (F : Map n p) (G : Map m q) (H : Map p r) (J : Map q s) :
    (tensorMap H J).comp (tensorMap F G)=tensorMap (H.comp F) (J.comp G) := by
  apply linearMap_eq_of_tensors
  intro A B
  simp only [LinearMap.comp_apply,tensorMap_kronecker]

lemma tensorMap_ad [DecidableEq n] [DecidableEq m] (S : Matrix p n ℂ) (T : Matrix q m ℂ) :
    tensorMap (ad S) (ad T)=ad (S ⊗ₖ T) := by
  apply linearMap_eq_of_tensors
  intro A B
  simp only [tensorMap_kronecker,ad_apply,Matrix.mul_kronecker_mul,Matrix.conjTranspose_kronecker]

lemma tensorMap_id [DecidableEq n] [DecidableEq m] :
    tensorMap (LinearMap.id : Map n n) (LinearMap.id : Map m m)=LinearMap.id := by
  apply linearMap_eq_of_tensors
  intro A B
  simp [tensorMap_kronecker]

lemma tensorMap_transpose [DecidableEq n] [DecidableEq m] :
    tensorMap (transposeMap : Map n n) (transposeMap : Map m m)=transposeMap := by
  apply linearMap_eq_of_tensors
  intro A B
  simp only [tensorMap_kronecker,transposeMap_apply,Matrix.kroneckerMap_transpose]

lemma cp_tensor_input_transpose [DecidableEq n] [DecidableEq m]
    {F : Map n p} {G : Map m q} (hF : CP (F.comp transposeMap))
    (hG : CP (G.comp transposeMap)) : CP ((tensorMap F G).comp transposeMap) := by
  rw [← tensorMap_transpose, tensorMap_comp]
  exact cp_tensorMap hF hG

lemma hsAdjoint_tensor_effect [DecidableEq n] [DecidableEq m]
    (F : Map n p) (G : Map m q) (A : Mat p) (B : Mat q) :
    hsAdjoint (tensorMap F G) (A ⊗ₖ B)=hsAdjoint F A ⊗ₖ hsAdjoint G B := by
  ext ⟨i,k⟩ ⟨j,l⟩
  change (∑ a, ∑ b, star (tensorMap F G (Matrix.single (i,k) (j,l) 1) a b) *
    (A ⊗ₖ B) a b) =
    (∑ a, ∑ b, star (F (Matrix.single i j 1) a b)*A a b) *
    (∑ a, ∑ b, star (G (Matrix.single k l 1) a b)*B a b)
  simp_rw [← single_product (i,k) (j,l),tensorMap_kronecker]
  have he (c d e f : ℂ) : star (c*d)*(e*f)=(star c*e)*(star d*f) := by
    simp only [star_mul]
    ring
  simp only [Matrix.kroneckerMap_apply,Fintype.sum_prod_type]
  simp_rw [he, ← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

lemma pullback_tensor [DecidableEq n] [DecidableEq m]
    {F : Map n p} {G : Map m q} (hF : CP F) (hG : CP G)
    (A : Mat p) (B : Mat q) (Z : Mat (n × m)) :
    Matrix.trace ((A ⊗ₖ B)*tensorMap F G Z)=
      Matrix.trace ((hsAdjoint F A ⊗ₖ hsAdjoint G B)*Z) := by
  rw [Matrix.trace_mul_comm,← trace_hsAdjoint (cp_tensorMap hF hG),hsAdjoint_tensor_effect,
    Matrix.trace_mul_comm]

lemma hsAdjoint_ad_comp [DecidableEq n] [DecidableEq m]
    {F : Map n m} (hF : CP F) (S : Mat n) (X : Mat m) :
    hsAdjoint (F.comp (ad S)) X=Sᴴ*hsAdjoint F X*S := by
  ext i j
  have h (Y : Mat n) : Matrix.trace (Y*hsAdjoint (F.comp (ad S)) X)=
      Matrix.trace (Y*(Sᴴ*hsAdjoint F X*S)) := by
    rw [trace_hsAdjoint (cp_comp hF (cp_ad S)),LinearMap.comp_apply,
      ← trace_hsAdjoint hF]
    simp only [ad_apply]
    calc
      Matrix.trace (S*Y*Sᴴ*hsAdjoint F X)=Matrix.trace (S*(Y*Sᴴ*hsAdjoint F X)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Y*Sᴴ*hsAdjoint F X)*S) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Y*(Sᴴ*hsAdjoint F X*S)) := by simp only [Matrix.mul_assoc]
  simpa only [Matrix.trace_single_mul,one_smul] using h (Matrix.single j i 1)
end SecretKey

end

end OAI
