import OAI.Analysis.IrrationalRotation.Operators.NormalTraceProjectionRigidity

namespace OAI

noncomputable section
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem NormalTraceProjectionRigidity.hasOnlyTrivialInvariantProjections_smul_iff
    (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) {c : ℂ} (hc : c ≠ 0) :
    HasOnlyTrivialInvariantProjections M (c • T) ↔
      HasOnlyTrivialInvariantProjections M T := by
  have hinv (p : H →L[ℂ] H) : (1 - p) * (c • T) * p = 0 ↔
      (1 - p) * T * p = 0 := by
    simp only [mul_smul_comm, smul_mul_assoc, smul_eq_zero, hc, false_or]
  constructor
  · intro h p hpm hp hT
    exact h p hpm hp ((hinv p).mpr hT)
  · intro h p hpm hp hT
    exact h p hpm hp ((hinv p).mp hT)

theorem hasOnlyTrivialInvariantProjections_of_trace_transport
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ) (A B : M)
    (hB : HasOnlyTrivialInvariantProjections M (B : H →L[ℂ] H))
    (htransport : ∀ p : M, IsStarProjection (p : H →L[ℂ] H) →
      (1 - (p : H →L[ℂ] H)) * (A : H →L[ℂ] H) * (p : H →L[ℂ] H) = 0 →
      ∃ P : M, IsStarProjection (P : H →L[ℂ] H) ∧
        (1 - (P : H →L[ℂ] H)) * (B : H →L[ℂ] H) * (P : H →L[ℂ] H) = 0 ∧
        τ P = τ p) :
    HasOnlyTrivialInvariantProjections M (A : H →L[ℂ] H) := by
  intro p hpm hp hinv
  let p' : M := ⟨p, hpm⟩
  obtain ⟨P, hP, hPinv, htrace⟩ := htransport p' hp hinv
  have htrivP := hB (P : H →L[ℂ] H) P.property hP hPinv
  have hnontriv := NormalTraceProjectionRigidity.nontrivial_iff_of_trace_eq
    τ hτ hp hP htrace.symm
  by_contra hpnontriv
  push Not at hpnontriv
  have hp' : p' ≠ 0 ∧ p' ≠ 1 := by
    constructor
    · intro h
      exact hpnontriv.1 (congrArg Subtype.val h)
    · intro h
      exact hpnontriv.2 (congrArg Subtype.val h)
  have hP' := hnontriv.mp hp'
  rcases htrivP with hz | ho
  · exact hP'.1 (Subtype.ext hz)
  · exact hP'.2 (Subtype.ext ho)

end Invariant233

end

end OAI
