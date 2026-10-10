import OAI.Analysis.Nuclearity.NuclearCommutingBound

namespace OAI

/-! The commuting representation of the minimal tensor product supplied by
the nuclear matrix approximation. No tensor norm uniqueness is assumed. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {B C E : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra C] [CStarAlgebra E]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [PartialOrder E] [StarOrderedRing E]

def commutingProductPolynomial (π : B →⋆ₙₐ[ℂ] E) (η : C →⋆ₐ[ℂ] E) :
    (B × C →₀ ℂ) →ₗ[ℂ] E :=
  Finsupp.linearCombination ℂ (fun p => π p.1 * η p.2)

lemma commutingProductPolynomial_bound (hB : Nuclear B)
    (π : B →⋆ₙₐ[ℂ] E) (η : C →⋆ₐ[ℂ] E) (hc : ∀ b c, Commute (π b) (η c))
    (d : B × C →₀ ℂ) :
    ‖commutingProductPolynomial π η d‖ ≤ 16 * ‖tensorPolynomial d‖ := by
  classical
  have h := nuclear_commuting_sum_norm_le hB π η hc d.support
    (fun p => d p • p.1) Prod.snd
  simpa only [commutingProductPolynomial, tensorPolynomial, Finsupp.linearCombination_apply,
    Finsupp.sum, map_smul, smul_mul_assoc, minimalElementary_smul_left] using h

def commutingMinimalLinear (π : B →⋆ₙₐ[ℂ] E) (η : C →⋆ₐ[ℂ] E) :
    MinimalTensor B C →L[ℂ] E :=
  (commutingProductPolynomial π η).extendOfNorm tensorPolynomial

lemma commutingMinimalLinear_polynomial (hB : Nuclear B)
    (π : B →⋆ₙₐ[ℂ] E) (η : C →⋆ₐ[ℂ] E) (hc : ∀ b c, Commute (π b) (η c))
    (d : B × C →₀ ℂ) :
    commutingMinimalLinear π η (tensorPolynomial d) = commutingProductPolynomial π η d :=
  LinearMap.extendOfNorm_eq tensorPolynomial_dense
    ⟨16, commutingProductPolynomial_bound hB π η hc⟩ d

lemma commutingMinimalLinear_elementary (hB : Nuclear B)
    (π : B →⋆ₙₐ[ℂ] E) (η : C →⋆ₐ[ℂ] E) (hc : ∀ b c, Commute (π b) (η c))
    (b : B) (c : C) : commutingMinimalLinear π η (minimalElementary b c) = π b * η c := by
  rw [← tensorPolynomial_single b c, commutingMinimalLinear_polynomial hB π η hc]
  simp [commutingProductPolynomial]

lemma commutingMinimalLinear_mul (hB : Nuclear B)
    (π : B →⋆ₙₐ[ℂ] E) (η : C →⋆ₐ[ℂ] E) (hc : ∀ b c, Commute (π b) (η c))
    (x y : MinimalTensor B C) :
    commutingMinimalLinear π η (x * y) = commutingMinimalLinear π η x * commutingMinimalLinear π η y := by
  let L := commutingMinimalLinear π η
  have hleft (b : B) (c : C) (y : MinimalTensor B C) :
      L (minimalElementary b c * y) = L (minimalElementary b c) * L y := by
    have hmaps : L.comp (ContinuousLinearMap.mul ℂ _ (minimalElementary b c)) =
        (ContinuousLinearMap.mul ℂ E (L (minimalElementary b c))).comp L := by
      apply minimalTensor_clm_ext
      intro b' c'
      change L (minimalElementary b c * minimalElementary b' c') =
        L (minimalElementary b c) * L (minimalElementary b' c')
      simp only [L, ← minimalElementary_mul, commutingMinimalLinear_elementary hB π η hc, map_mul]
      simp only [mul_assoc]
      rw [← mul_assoc (π b') (η c) (η c'), (hc b' c).eq, mul_assoc]
    exact DFunLike.congr_fun hmaps y
  have hmaps : L.comp ((ContinuousLinearMap.mul ℂ _).flip y) =
      ((ContinuousLinearMap.mul ℂ E).flip (L y)).comp L := by
    apply minimalTensor_clm_ext
    exact fun b c => hleft b c y
  exact DFunLike.congr_fun hmaps x

lemma commutingMinimalLinear_star (hB : Nuclear B)
    (π : B →⋆ₙₐ[ℂ] E) (η : C →⋆ₐ[ℂ] E) (hc : ∀ b c, Commute (π b) (η c))
    (x : MinimalTensor B C) :
    commutingMinimalLinear π η (star x) = star (commutingMinimalLinear π η x) := by
  let L := commutingMinimalLinear π η
  let S : Submodule ℂ (MinimalTensor B C) :=
    { carrier := {z | L (star z) = star (L z)}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at *
        simp only [star_add, map_add, ha, hb]
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_ofPred_eq] at *
        simp only [star_smul, map_smul, hz] }
  have hS : S = ⊤ := by
    apply minimal_elementary_span_dense S
      (isClosed_eq (L.continuous.comp continuous_star) L.continuous.star)
    intro b c
    change L (star (minimalElementary b c)) = star (L (minimalElementary b c))
    simp only [L, ← minimalElementary_star, commutingMinimalLinear_elementary hB π η hc,
      map_star, star_mul]
    simpa only [star_mul] using congrArg star (hc b c).eq.symm
  have hx : x ∈ S := by rw [hS]; trivial
  exact hx

def nuclearCommutingRepresentation (hB : Nuclear B)
    (π : B →⋆ₙₐ[ℂ] E) (η : C →⋆ₐ[ℂ] E) (hc : ∀ b c, Commute (π b) (η c)) :
    MinimalTensor B C →⋆ₙₐ[ℂ] E where
  toFun := commutingMinimalLinear π η
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := commutingMinimalLinear_mul hB π η hc
  map_star' := commutingMinimalLinear_star hB π η hc

end WeakPureInfiniteness

end

end OAI
