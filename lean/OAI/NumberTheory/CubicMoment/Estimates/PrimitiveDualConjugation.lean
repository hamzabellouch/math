import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveDualMoments

namespace OAI

/-! Conjugation preserves the normalized dual moment and reverses the
Mellin height. Thus the cubic sieve controls the actual dual coefficients. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma star_mellinPhase (u x : ℝ) : star (mellinPhase u x) = mellinPhase (-u) x := by
  change (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul,Complex.ofReal_neg]
  ring

lemma star_normalizedDualPolynomial {ν : Type*} (S : Finset ν) (χ : ν → ℂ)
    (N : ν → ℝ) (J u : ℝ) :
    star (normalizedDualPolynomial S χ N J u) =
      normalizedDualPolynomial S (fun v => star (χ v)) N J (-u) := by
  simp only [normalizedDualPolynomial,star_sum,star_mul,star_mellinPhase,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro v hv
  ring

lemma residueIdealChar_star {q : Eisenstein} (ψ : MulChar (Residues q) ℂ)
    (ν : EisensteinIdealExponent) :
    residueIdealChar q (star ψ) ν = star (residueIdealChar q ψ ν) := rfl

lemma norm_dual_conjugate {q : Eisenstein} (ψ : MulChar (Residues q) ℂ)
    (S : Finset EisensteinIdealExponent) (J u : ℝ) :
    ‖normalizedDualPolynomial S (residueIdealChar q (star ψ)) idealExponentNorm J u‖ =
      ‖normalizedDualPolynomial S (residueIdealChar q ψ) idealExponentNorm J (-u)‖ := by
  rw [← norm_star (normalizedDualPolynomial S (residueIdealChar q ψ) idealExponentNorm J (-u)),
    star_normalizedDualPolynomial,neg_neg]
  rfl

end CubicFirstMoment

end

end OAI
