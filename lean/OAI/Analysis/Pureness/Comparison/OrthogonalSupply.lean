import OAI.Analysis.Pureness.Comparison.SpectralSplitting
import OAI.Analysis.Pureness.Comparison.ScalarCorners
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.LinearAlgebra.Complex.Module

namespace OAI
open scoped ComplexStarModule
open Complex
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma hereditary_projection_right_identity {q x : A} (hq : IsStarProjection q)
    (hx : x ∈ hereditaryCorner q hq.nonneg) : x * q = x := by
  have hz := hereditaryCorner_mul_eq_zero hq.nonneg
    (c := 1 - q) (by rw [mul_sub, mul_one, hq.isIdempotentElem.eq, sub_self]) hx
  rw [mul_sub, mul_one] at hz
  exact (sub_eq_zero.mp hz).symm

lemma scalar_of_no_orthogonal_pair {q : A} (hq : IsStarProjection q)
    (hno : ∀ c d : A, 0 ≤ c → 0 ≤ d → c ∈ hereditaryCorner q hq.nonneg →
      d ∈ hereditaryCorner q hq.nonneg → c * d = 0 → c = 0 ∨ d = 0)
    {b : A} (hb : 0 ≤ b) (hmem : b ∈ hereditaryCorner q hq.nonneg) :
    ∃ z : ℂ, b = z • q := by
  by_cases hbn : b = 0
  · exact ⟨0, by simp [hbn]⟩
  rcases positive_scalar_projection_or_orthogonal_pair hb hbn with h | h
  · obtain ⟨r, hr, p, hp, hpn, hpm, hfactor⟩ := h
    have hpqmem := hereditaryCorner_le_of_mem hq.nonneg hb hmem hpm
    have hpq := hereditary_projection_right_identity hq hpqmem
    have hdiff := hp.sub_of_mul_eq_left hq hpq
    have hz : p * (q - p) = 0 := by
      rw [mul_sub, hpq, hp.isIdempotentElem.eq, sub_self]
    have heq := hno p (q - p) hp.nonneg hdiff.nonneg hpqmem
      ((hereditaryCorner q hq.nonneg).sub_mem (self_mem_hereditaryCorner q hq.nonneg) hpqmem) hz
    have hpqeq : p = q := by
      rcases heq with h | h
      · exact (hpn h).elim
      · exact (sub_eq_zero.mp h).symm
    refine ⟨(r : ℂ), ?_⟩
    simpa only [hpqeq, Complex.coe_smul] using hfactor
  · obtain ⟨c, d, hc, hd, hcn, hdn, hcd, hcm, hdm⟩ := h
    exact ((hno c d hc hd (hereditaryCorner_le_of_mem hq.nonneg hb hmem hcm)
      (hereditaryCorner_le_of_mem hq.nonneg hb hmem hdm) hcd).elim hcn hdn).elim

lemma scalar_sandwich_of_positive_sandwich {q : A}
    (hpos : ∀ b : A, 0 ≤ b → ∃ z : ℂ, q * b * q = z • q) :
    ∀ a : A, ∃ z : ℂ, q * a * q = z • q := by
  have hself : ∀ a : A, IsSelfAdjoint a → ∃ z : ℂ, q * a * q = z • q := by
    intro a ha
    obtain ⟨z, hz⟩ := hpos a⁺ (CFC.posPart_nonneg a)
    obtain ⟨w, hw⟩ := hpos a⁻ (CFC.negPart_nonneg a)
    refine ⟨z - w, ?_⟩
    conv_lhs => rw [← CFC.posPart_sub_negPart a ha]
    rw [mul_sub, sub_mul, hz, hw, sub_smul]
  intro a
  obtain ⟨z, hz⟩ := hself (ℜ a) (ℜ a).property
  obtain ⟨w, hw⟩ := hself (ℑ a) (ℑ a).property
  refine ⟨z + I * w, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart a]
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hz, hw, smul_smul, add_smul]

theorem exists_orthogonal_positive_pair [IsSimpleCStarAlgebra A]
    (hinfinite : ¬ FiniteDimensional ℂ A) {b : A} (hb : 0 ≤ b) (hbn : b ≠ 0) :
    ∃ c d : A, 0 ≤ c ∧ 0 ≤ d ∧ c ≠ 0 ∧ d ≠ 0 ∧ c * d = 0 ∧
      c ∈ hereditaryCorner b hb ∧ d ∈ hereditaryCorner b hb := by
  classical
  by_contra hno
  have hnopair : ∀ c d : A, 0 ≤ c → 0 ≤ d →
      c ∈ hereditaryCorner b hb → d ∈ hereditaryCorner b hb →
      c * d = 0 → c = 0 ∨ d = 0 := by
    intro c d hc hd hcm hdm hcd
    by_contra h
    push Not at h
    exact hno ⟨c, d, hc, hd, h.1, h.2, hcd, hcm, hdm⟩
  rcases positive_scalar_projection_or_orthogonal_pair hb hbn with h | h
  · obtain ⟨r, hr, q, hq, hqn, hqm, hfactor⟩ := h
    have hle := hereditaryCorner_le_of_mem hb hq.nonneg hqm
    apply hinfinite
    apply finiteDimensional_of_scalar_corner hq.nonneg hqn
    apply scalar_sandwich_of_positive_sandwich
    intro a ha
    apply scalar_of_no_orthogonal_pair hq
    · intro c d hc hd hcm hdm hcd
      exact hnopair c d hc hd (hle hcm) (hle hdm) hcd
    · simpa only [hq.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg ha q
    · exact subset_closure ⟨a, rfl⟩
  · exact hno h
end CuntzComparison

end OAI
