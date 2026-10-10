import Mathlib.Analysis.Meromorphic.NormalForm
import OAI.NumberTheory.SiegelZeros.EntireFunctions.AvoidZeroRadii
import OAI.NumberTheory.SiegelZeros.EntireFunctions.EntireLogarithm

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W51

open Filter Set
open scoped Topology

variable {q : ℕ} [NeZero q]

noncomputable def normalizedQuotient (χ : DirichletCharacter ℂ q) (P : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (normalizedCompletion χ / P) univ

theorem normalizedQuotient_meromorphic (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (P : ℂ → ℂ) (hP : Differentiable ℂ P) :
    MeromorphicOn (normalizedCompletion χ / P) univ := by
  intro z _
  exact ((differentiable_normalizedCompletion χ hχ).analyticAt z).meromorphicAt.div
    (hP.analyticAt z).meromorphicAt

theorem meromorphicOrderAt_normalizedQuotient_eq_zero
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (P : ℂ → ℂ)
    (hP : Differentiable ℂ P)
    (horders : ∀ z, analyticOrderAt P z = analyticOrderAt (normalizedCompletion χ) z)
    (z : ℂ) : meromorphicOrderAt (normalizedQuotient χ P) z = 0 := by
  have hf := (differentiable_normalizedCompletion χ hχ).analyticAt z
  have hp := hP.analyticAt z
  have hm := normalizedQuotient_meromorphic χ hχ P hP
  unfold normalizedQuotient
  rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ z),
    meromorphicOrderAt_div hf.meromorphicAt hp.meromorphicAt,
    hf.meromorphicOrderAt_eq, hp.meromorphicOrderAt_eq, horders]
  rw [← natCast_order_normalizedCompletion χ hχ z]
  simp

theorem normalizedQuotient_entire_ne_zero
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (P : ℂ → ℂ)
    (hP : Differentiable ℂ P)
    (horders : ∀ z, analyticOrderAt P z = analyticOrderAt (normalizedCompletion χ) z) :
    Differentiable ℂ (normalizedQuotient χ P) ∧
      ∀ z, normalizedQuotient χ P z ≠ 0 := by
  have hnf : MeromorphicNFOn (normalizedQuotient χ P) univ :=
    meromorphicNFOn_toMeromorphicNFOn _ _
  have ho := meromorphicOrderAt_normalizedQuotient_eq_zero χ hχ P hP horders
  constructor
  · intro z
    exact ((hnf (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by rw [ho])).differentiableAt
  · intro z
    exact (hnf (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mp (ho z)

theorem normalizedQuotient_eq_div (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (P : ℂ → ℂ) (hP : Differentiable ℂ P) {z : ℂ} (hz : P z ≠ 0) :
    normalizedQuotient χ P z = normalizedCompletion χ z / P z := by
  have ha := ((differentiable_normalizedCompletion χ hχ).analyticAt z).div
    (hP.analyticAt z) hz
  unfold normalizedQuotient
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt
    (normalizedQuotient_meromorphic χ hχ P hP) (mem_univ z),
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]
  rfl

theorem normalizedQuotient_mul (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (P : ℂ → ℂ) (hP : Differentiable ℂ P)
    (horders : ∀ z, analyticOrderAt P z = analyticOrderAt (normalizedCompletion χ) z)
    (z : ℂ) : normalizedQuotient χ P z * P z = normalizedCompletion χ z := by
  by_cases hz : P z = 0
  · have ho : analyticOrderAt (normalizedCompletion χ) z ≠ 0 := by
      rw [← horders]
      exact (hP.analyticAt z).analyticOrderAt_ne_zero.mpr hz
    have hfz := apply_eq_zero_of_analyticOrderAt_ne_zero ho
    simp only [hz, hfz, mul_zero]
  · rw [normalizedQuotient_eq_div χ hχ P hP hz, div_mul_cancel₀ _ hz]

theorem exists_entire_logarithm_normalizedQuotient
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (P : ℂ → ℂ)
    (hP : Differentiable ℂ P)
    (horders : ∀ z, analyticOrderAt P z = analyticOrderAt (normalizedCompletion χ) z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ z, normalizedCompletion χ z = Complex.exp (g z) * P z := by
  obtain ⟨hd, hn⟩ := normalizedQuotient_entire_ne_zero χ hχ P hP horders
  obtain ⟨g, hg, heq⟩ := W03.exists_entire_logarithm (normalizedQuotient χ P) hd hn
  refine ⟨g, hg, fun z => ?_⟩
  rw [← heq]
  exact (normalizedQuotient_mul χ hχ P hP horders z).symm

end SiegelZerosAwei.W51

end

end SiegelZeros

end OAI
