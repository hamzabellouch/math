import OAI.Analysis.KadisonKastler.CentralSpectralContraction
import OAI.Analysis.KadisonKastler.SelfAdjointAveraging

namespace OAI

/-! # Arbitrarily accurate finite averages toward the center -/

namespace KadisonKastler

open Generator.Tracial
open scoped ComplexStarModule

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace FiniteInnerAverage

/-- The one-term average. -/
def identity (M : VonNeumannAlgebra H) : FiniteInnerAverage M where
  Index := Unit
  fintype := inferInstance
  nonempty := inferInstance
  unitary _ := 1

@[simp] theorem identity_apply (x : H →L[ℂ] H) : (identity M).apply x = x := by
  change finiteAverage (fun _ : Unit =>
    unitaryConj (ambientAlgebraUnitary (1 : _root_.unitary (Algebra M))) x) = x
  have h : unitaryConj (ambientAlgebraUnitary (1 : _root_.unitary (Algebra M))) x = x := by
    change (1 : H →L[ℂ] H) * x * star (1 : H →L[ℂ] H) = x
    simp
  rw [h]
  exact finiteAverage_const x

/-- Every inner average fixes every central element. -/
theorem apply_central (A : FiniteInnerAverage M) (z : Algebra (concreteCenter M)) :
    A.apply z.val = z.val := by
  have h (i : A.Index) : unitaryConj (ambientAlgebraUnitary (A.unitary i)) z.val = z.val := by
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp z.property.2
      ((A.unitary i : Algebra M) : H →L[ℂ] H) (A.unitary i : Algebra M).property
    change ((A.unitary i : Algebra M) : H →L[ℂ] H) * z.val *
      star ((A.unitary i : Algebra M) : H →L[ℂ] H) = z.val
    rw [hc, mul_assoc]
    have hu : ((A.unitary i : Algebra M) : H →L[ℂ] H) *
        star ((A.unitary i : Algebra M) : H →L[ℂ] H) = 1 :=
      congrArg Subtype.val (Unitary.mul_star_self_of_mem (A.unitary i).property)
    rw [hu, mul_one]
  change finiteAverage (fun i => unitaryConj (ambientAlgebraUnitary (A.unitary i)) z.val) = _
  simp only [h]
  exact finiteAverage_const _

end FiniteInnerAverage

/-- The concrete center included in the original algebra. -/
def centralInclusion : Algebra (concreteCenter M) →⋆ₐ[ℂ] Algebra M :=
  StarSubalgebra.inclusion (fun _ hx => hx.1)

/-- Iteration of the uniform contraction gives a geometric error estimate. -/
theorem exists_selfAdjoint_central_average_power [Nontrivial H]
    (x : Algebra M) (hx : IsSelfAdjoint x) (n : ℕ) :
    ∃ (A : FiniteInnerAverage M) (c : Algebra (concreteCenter M)),
      IsSelfAdjoint c ∧ ‖A.apply x.val - c.val‖ ≤ (3 / 4 : ℝ)^n * ‖x‖ := by
  induction n with
  | zero =>
    refine ⟨FiniteInnerAverage.identity M, 0, star_zero _, ?_⟩
    simp only [FiniteInnerAverage.identity_apply, ZeroMemClass.coe_zero, sub_zero, pow_zero, one_mul]
    rfl
  | succ n ih =>
    obtain ⟨A, c, hc, hA⟩ := ih
    let y : Algebra M := A.algebraApply x - centralInclusion c
    have hy : IsSelfAdjoint y := (A.algebraApply_selfAdjoint x hx).sub (hc.map centralInclusion)
    obtain ⟨B, d, hd, hB⟩ := exists_central_spectral_contraction y hy
    refine ⟨B.comp A, c + d, hc.add hd, ?_⟩
    have he : (B.comp A).apply x.val - (c + d).val = B.apply y.val - d.val := by
      rw [FiniteInnerAverage.comp_apply]
      change B.apply (A.apply x.val) - (c.val + d.val) =
        B.apply ((A.algebraApply x).val - c.val) - d.val
      rw [B.apply_sub, B.apply_central, A.algebraApply_val]
      abel
    rw [he]
    apply hB.trans
    have hn : ‖y‖ = ‖A.apply x.val - c.val‖ := by
      change ‖(A.algebraApply x).val - c.val‖ = _
      rw [A.algebraApply_val]
    rw [hn, pow_succ]
    nlinarith

/-- Self-adjoint elements have finite averages arbitrarily close to the center. -/
theorem exists_selfAdjoint_central_average [Nontrivial H]
    (x : Algebra M) (hx : IsSelfAdjoint x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : FiniteInnerAverage M) (c : Algebra (concreteCenter M)),
      IsSelfAdjoint c ∧ ‖A.apply x.val - c.val‖ < ε := by
  have ht : Filter.Tendsto (fun n : ℕ => (3 / 4 : ℝ)^n * ‖x‖)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)).mul_const ‖x‖
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨A, c, hc, hA⟩ := exists_selfAdjoint_central_average_power x hx n
  exact ⟨A, c, hc, hA.trans_lt hn⟩

/-- Two successive self-adjoint averages handle every element of the algebra. -/
theorem exists_central_average [Nontrivial H] (x : Algebra M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : FiniteInnerAverage M) (c : Algebra (concreteCenter M)),
      ‖A.apply x.val - c.val‖ < ε := by
  let a : Algebra M := ℜ x
  let b : Algebra M := ℑ x
  obtain ⟨A, c, _, hA⟩ := exists_selfAdjoint_central_average a (ℜ x).property (ε / 2) (by positivity)
  let b' := A.algebraApply b
  obtain ⟨B, d, _, hB⟩ := exists_selfAdjoint_central_average b'
    (A.algebraApply_selfAdjoint b (ℑ x).property) (ε / 2) (by positivity)
  have hc : ‖B.apply (A.apply a.val) - c.val‖ < ε / 2 := by
    rw [← B.apply_central c]
    exact (B.norm_apply_sub_le _ _).trans_lt hA
  have hd : ‖B.apply (A.apply b.val) - d.val‖ < ε / 2 := by
    simpa only [b', FiniteInnerAverage.algebraApply_val] using hB
  have hx : x.val = a.val + Complex.I • b.val :=
    (congrArg Subtype.val (realPart_add_I_smul_imaginaryPart x)).symm
  refine ⟨B.comp A, c + Complex.I • d, ?_⟩
  have he : (B.comp A).apply x.val - (c + Complex.I • d).val =
      (B.apply (A.apply a.val) - c.val) +
        Complex.I • (B.apply (A.apply b.val) - d.val) := by
    rw [FiniteInnerAverage.comp_apply, hx]
    change B.linear (A.linear (a.val + Complex.I • b.val)) - _ = _
    rw [A.linear.map_add, A.linear.map_smul, B.linear.map_add, B.linear.map_smul]
    change (B.apply (A.apply a.val) + Complex.I • B.apply (A.apply b.val)) -
      (c.val + Complex.I • d.val) = _
    module
  rw [he]
  have hn := norm_add_le (B.apply (A.apply a.val) - c.val)
    (Complex.I • (B.apply (A.apply b.val) - d.val))
  rw [norm_smul, Complex.norm_I, one_mul] at hn
  linarith

end

end KadisonKastler

end OAI
