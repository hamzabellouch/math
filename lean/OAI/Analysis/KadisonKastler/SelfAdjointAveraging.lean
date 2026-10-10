import OAI.Analysis.KadisonKastler.FiniteInnerComposition

namespace OAI

/-! # Passing from self-adjoint to arbitrary operator averaging -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexStarModule

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

omit [Nontrivial H] in
/-- Average the real part, then the self-adjoint averaged imaginary part.
The second contraction preserves the first scalar approximation. -/
theorem exists_scalar_average_of_selfAdjoint
    (havg : ∀ (y : Algebra M), IsSelfAdjoint y → ∀ δ : ℝ, 0 < δ →
      ∃ (A : FiniteInnerAverage M) (z : ℂ),
        ‖A.apply y.val - z • (1 : H →L[ℂ] H)‖ < δ)
    (x : Algebra M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (C : FiniteInnerAverage M) (z : ℂ),
      ‖C.apply x.val - z • (1 : H →L[ℂ] H)‖ < ε := by
  let a : Algebra M := ℜ x
  let b : Algebra M := ℑ x
  have ha : IsSelfAdjoint a := (ℜ x).property
  have hb : IsSelfAdjoint b := (ℑ x).property
  obtain ⟨A, z, hA⟩ := havg a ha
    (ε / 2) (by positivity)
  let b' := A.algebraApply b
  obtain ⟨B, w, hB⟩ := havg b' (A.algebraApply_selfAdjoint b hb)
    (ε / 2) (by positivity)
  have hB' : ‖B.apply (A.apply b.val) - w • (1 : H →L[ℂ] H)‖ < ε / 2 := by
    simpa only [b', FiniteInnerAverage.algebraApply_val] using hB
  have hA' : ‖B.apply (A.apply a.val) - z • (1 : H →L[ℂ] H)‖ < ε / 2 := by
    rw [← B.apply_scalar z]
    exact (B.norm_apply_sub_le _ _).trans_lt hA
  have hx : x.val = a.val + Complex.I • b.val := by
    exact (congrArg Subtype.val (realPart_add_I_smul_imaginaryPart x)).symm
  refine ⟨B.comp A, z + Complex.I * w, ?_⟩
  have he : (B.comp A).apply x.val - (z + Complex.I * w) • (1 : H →L[ℂ] H) =
      (B.apply (A.apply a.val) - z • 1) +
        Complex.I • (B.apply (A.apply b.val) - w • 1) := by
    rw [FiniteInnerAverage.comp_apply, hx]
    change B.linear (A.linear (a.val + Complex.I • b.val)) - _ = _
    rw [A.linear.map_add, A.linear.map_smul, B.linear.map_add, B.linear.map_smul]
    change (B.apply (A.apply a.val) + Complex.I • B.apply (A.apply b.val)) -
      (z + Complex.I * w) • (1 : H →L[ℂ] H) = _
    simp only [add_smul, smul_smul, smul_sub]
    abel
  rw [he]
  calc
    ‖(B.apply (A.apply a.val) - z • 1) +
        Complex.I • (B.apply (A.apply b.val) - w • 1)‖ ≤
        ‖B.apply (A.apply a.val) - z • 1‖ +
          ‖Complex.I • (B.apply (A.apply b.val) - w • 1)‖ := norm_add_le _ _
    _ = ‖B.apply (A.apply a.val) - z • 1‖ +
        ‖B.apply (A.apply b.val) - w • 1‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    _ < ε := by linarith

end

end KadisonKastler

end OAI
