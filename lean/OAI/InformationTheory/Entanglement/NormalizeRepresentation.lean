import OAI.InformationTheory.Entanglement.TensorTools
import OAI.InformationTheory.Entanglement.EffectNormalization

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n m p q : Type} [Fintype n] [Fintype m] [Fintype p] [Fintype q]
  [DecidableEq n] [DecidableEq m] [DecidableEq p] [DecidableEq q]

lemma ad_one : ad (1 : Mat n)=LinearMap.id := by
  ext A i j
  simp [ad_apply]

omit [DecidableEq p] [DecidableEq q] in
lemma tensorMap_ad_left (F : Map n p) (G : Map m q) (S : Mat n) :
    tensorMap (F.comp (ad S)) G=(tensorMap F G).comp (ad (S ⊗ₖ (1 : Mat m))) := by
  rw [← tensorMap_ad,ad_one,tensorMap_comp]
  simp

omit [Fintype p] [DecidableEq n] [DecidableEq p] in
lemma cp_ad_input_transpose {F : Map n p} (hFT : CP (F.comp transposeMap)) (S : Mat n) :
    CP ((F.comp (ad S)).comp transposeMap) := by
  have he : (ad S).comp transposeMap = transposeMap.comp (ad (Sᴴ)ᵀ) := by
    have hs : ((Sᴴ)ᵀ)ᴴ=Sᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    ext A i j
    simp only [LinearMap.comp_apply,transposeMap_apply,ad_apply,hs,
      Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
  rw [LinearMap.comp_assoc,he,← LinearMap.comp_assoc]
  exact cp_comp hFT (cp_ad _)

omit [DecidableEq q] in
lemma normalized_representation (R : Mat (p × q)) (hR : Represented R)
    (X : Fin 2 → Mat p) (hX : ∀ i, (X i).PosSemidef) :
    ∃ r s : ℕ, 0<r ∧ 0<s ∧
      ∃ (L : Map (Fin r) p) (M : Map (Fin s) q) (χ : Fin r × Fin s → ℂ),
        CP L ∧ CP (L.comp transposeMap) ∧ CP M ∧ CP (M.comp transposeMap) ∧
        R=tensorMap L M (projector χ) ∧ Commute (hsAdjoint L (X 0)) (hsAdjoint L (X 1)) := by
  obtain ⟨_,_,r,s,hr,hs,L,M,χ,hL,hLT,hM,hMT,hR⟩ := hR
  have hA (i : Fin 2) := cp_positive (cp_hsAdjoint hL) (hX i)
  obtain ⟨S,T,hST,hTS,hcomm⟩ := commuting_normalization (hA 0) (hA 1)
  refine ⟨r,s,hr,hs,L.comp (ad S),M,(T ⊗ₖ (1 : Mat (Fin s))).mulVec χ,
    cp_comp hL (cp_ad S),cp_ad_input_transpose hLT S,hM,hMT,?_,?_⟩
  · rw [tensorMap_ad_left,LinearMap.comp_apply,← ad_projector,hR]
    congr 1
    symm
    rw [ad_apply,ad_apply]
    have hprod : (S ⊗ₖ (1 : Mat (Fin s)))*(T ⊗ₖ (1 : Mat (Fin s)))=1 := by
      rw [← Matrix.mul_kronecker_mul,hST,Matrix.one_mul,Matrix.one_kronecker_one]
    calc
      (S ⊗ₖ 1) * ((T ⊗ₖ 1) * projector χ * (T ⊗ₖ 1)ᴴ) * (S ⊗ₖ 1)ᴴ =
        ((S ⊗ₖ 1)*(T ⊗ₖ 1))*projector χ*((S ⊗ₖ 1)*(T ⊗ₖ 1))ᴴ := by
          simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = projector χ := by rw [hprod,Matrix.conjTranspose_one,Matrix.one_mul,Matrix.mul_one]
  · rw [hsAdjoint_ad_comp hL,hsAdjoint_ad_comp hL]
    exact hcomm
end SecretKey

end

end OAI
