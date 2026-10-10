import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Model
import OAI.RepresentationTheory.PartialPermutation.SchurAverage

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra

namespace PartialPermutation

section MatrixCoefficients
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) [Representation.IsIrreducible ρ]
include hρ

lemma matrixCoefficient_orthogonality (x y u v : V) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, inner ℂ x (ρ g u) * conj (inner ℂ y (ρ g v)) =
      (inner ℂ v u / (Module.finrank ℂ V : ℂ)) * inner ℂ x y := by
  have h := congrArg (fun A : Module.End ℂ V => inner ℂ x (A y))
    (conjugateAverage_eq_trace ρ (InnerProductSpace.rankOne ℂ u v).toLinearMap)
  have hu (g : G) : inner ℂ v (ρ g⁻¹ y) = conj (inner ℂ y (ρ g v)) := by
    rw [← inner_conj_symm]
    have ht := hρ g v (ρ g⁻¹ y)
    simpa using ht.symm
  simpa [conjugateAverage, LinearMap.sum_apply, InnerProductSpace.rankOne_apply,
    InnerProductSpace.trace_rankOne, inner_smul_right, inner_sum, hu, mul_comm] using h

lemma normalized_matrixCoefficients_orthonormal {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ V) :
    Orthonormal ℂ (fun p : ι × ι =>
      (Real.sqrt ((Module.finrank ℂ V : ℝ) / Fintype.card G) : ℂ) •
        (WithLp.toLp 2 (fun g : G => conj (inner ℂ (e p.1) (ρ g (e p.2)))))) := by
  classical
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hD : (0 : ℝ) < Module.finrank ℂ V := by exact_mod_cast Module.finrank_pos (R := ℂ) (M := V)
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hDc : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hNc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have ht : (Real.sqrt ((Module.finrank ℂ V : ℝ) / Fintype.card G) : ℂ) ^ 2 =
      (Module.finrank ℂ V : ℂ) / Fintype.card G := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (div_nonneg hD.le hN.le)]
    push_cast
    rfl
  rw [orthonormal_iff_ite]
  intro p q
  rw [inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, PiLp.inner_apply, RCLike.inner_apply,
    starRingEnd_self_apply]
  simp_rw [mul_comm (conj (inner ℂ (e q.1) (ρ _ (e q.2))))]
  have h := matrixCoefficient_orthogonality ρ hρ (e p.1) (e q.1) (e p.2) (e q.2)
  have hs : ∑ g : G, inner ℂ (e p.1) (ρ g (e p.2)) *
      conj (inner ℂ (e q.1) (ρ g (e q.2))) =
      (Fintype.card G : ℂ) * ((inner ℂ (e q.2) (e p.2) /
        (Module.finrank ℂ V : ℂ)) * inner ℂ (e p.1) (e q.1)) := by
    rw [← h]
    field_simp
  rw [hs, orthonormal_iff_ite.mp e.orthonormal, orthonormal_iff_ite.mp e.orthonormal]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2
  · have hpq : p = q := Prod.ext h1 h2
    simp only [ite_eq_left, hpq, ← mul_assoc, ← pow_two, ht]
    field_simp
  · simp [h1, h2, Ne.symm h2, Prod.ext_iff]
  · simp [h1, h2, Prod.ext_iff]
  · simp [h1, h2, Prod.ext_iff]

end MatrixCoefficients
end PartialPermutation

end

end OAI
