import OAI.Analysis.Nuclearity.NuclearCommutingCPBound
import OAI.Analysis.Nuclearity.CommutingCPGram
import OAI.Analysis.WeakInfiniteness.NuclearApproximation
import OAI.Analysis.Nuclearity.DensePositiveExtension

namespace OAI

/-! The positive map on the minimal tensor product defined by a completely
positive map and a commuting representation. This is the functional
construction needed in KR02 Lemma 7.18, specialized to a nuclear first factor. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {B C E : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra C] [CStarAlgebra E]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [PartialOrder E] [StarOrderedRing E]

local instance cpTensorOrder : PartialOrder (MinimalTensor B C) := CStarAlgebra.spectralOrder _
local instance cpTensorOrdered : StarOrderedRing (MinimalTensor B C) := CStarAlgebra.spectralOrderedRing _

def cpCommutingPolynomial (f : B →L[ℂ] E) (η : C →⋆ₐ[ℂ] E) :
    (B × C →₀ ℂ) →ₗ[ℂ] E :=
  Finsupp.linearCombination ℂ (fun p => f p.1 * η p.2)

lemma cpCommutingPolynomial_bound (hB : Nuclear B)
    (f : B →L[ℂ] E) (hf : CompletelyPositive f) (η : C →⋆ₐ[ℂ] E)
    (hc : ∀ b c, Commute (f b) (η c)) (d : B × C →₀ ℂ) :
    ‖cpCommutingPolynomial f η d‖ ≤ (16 * (‖f‖ + 1)) * ‖tensorPolynomial d‖ := by
  classical
  have h := nuclear_commuting_cp_sum_norm_le hB f hf η hc d.support
    (fun p => d p • p.1) Prod.snd
  simpa only [cpCommutingPolynomial, tensorPolynomial, Finsupp.linearCombination_apply,
    Finsupp.sum, map_smul, smul_mul_assoc, minimalElementary_smul_left] using h

def cpCommutingLinear (f : B →L[ℂ] E) (η : C →⋆ₐ[ℂ] E) : MinimalTensor B C →L[ℂ] E :=
  (cpCommutingPolynomial f η).extendOfNorm tensorPolynomial

lemma cpCommutingLinear_polynomial (hB : Nuclear B)
    (f : B →L[ℂ] E) (hf : CompletelyPositive f) (η : C →⋆ₐ[ℂ] E)
    (hc : ∀ b c, Commute (f b) (η c)) (d : B × C →₀ ℂ) :
    cpCommutingLinear f η (tensorPolynomial d) = cpCommutingPolynomial f η d :=
  LinearMap.extendOfNorm_eq tensorPolynomial_dense
    ⟨16 * (‖f‖ + 1), cpCommutingPolynomial_bound hB f hf η hc⟩ d

lemma cpCommutingLinear_elementary (hB : Nuclear B)
    (f : B →L[ℂ] E) (hf : CompletelyPositive f) (η : C →⋆ₐ[ℂ] E)
    (hc : ∀ b c, Commute (f b) (η c)) (b : B) (c : C) :
    cpCommutingLinear f η (minimalElementary b c) = f b * η c := by
  rw [← tensorPolynomial_single b c, cpCommutingLinear_polynomial hB f hf η hc]
  simp [cpCommutingPolynomial]

lemma cpCommutingLinear_polynomial_square_nonneg (hB : Nuclear B)
    (f : B →L[ℂ] E) (hf : CompletelyPositive f) (η : C →⋆ₐ[ℂ] E)
    (hc : ∀ b c, Commute (f b) (η c)) (d : B × C →₀ ℂ) :
    0 ≤ cpCommutingLinear f η (star (tensorPolynomial d) * tensorPolynomial d) := by
  classical
  let b (p : d.support) := d p.val • p.val.1
  let c (p : d.support) := p.val.2
  have hd : tensorPolynomial d = ∑ p : d.support, minimalElementary (b p) (c p) := by
    rw [tensorPolynomial_eq_sum]
    exact (Finset.sum_coe_sort d.support (fun p => minimalElementary (d p • p.1) p.2)).symm
  rw [hd]
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, ← minimalElementary_star,
    ← minimalElementary_mul, map_sum, cpCommutingLinear_elementary hB f hf η hc]
  rw [Finset.sum_comm]
  exact commuting_cp_gram_nonneg f hf η.toNonUnitalStarAlgHom hc b c

lemma cpCommutingLinear_nonneg (hB : Nuclear B)
    (f : B →L[ℂ] E) (hf : CompletelyPositive f) (η : C →⋆ₐ[ℂ] E)
    (hc : ∀ b c, Commute (f b) (η c)) (x : MinimalTensor B C) (hx : 0 ≤ x) :
    0 ≤ cpCommutingLinear f η x :=
  continuousLinearMap_nonneg_of_dense_squares (cpCommutingLinear f η) tensorPolynomial
    tensorPolynomial_dense (cpCommutingLinear_polynomial_square_nonneg hB f hf η hc) x hx

def cpCommutingPositiveMap (hB : Nuclear B)
    (f : B →L[ℂ] E) (hf : CompletelyPositive f) (η : C →⋆ₐ[ℂ] E)
    (hc : ∀ b c, Commute (f b) (η c)) : MinimalTensor B C →ₚ[ℂ] E :=
  PositiveLinearMap.mk₀ (cpCommutingLinear f η).toLinearMap
    (cpCommutingLinear_nonneg hB f hf η hc)

end WeakPureInfiniteness

end

end OAI
