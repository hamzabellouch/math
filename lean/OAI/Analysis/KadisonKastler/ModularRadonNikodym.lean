import OAI.Analysis.KadisonKastler.CommutantPolarSupport
import OAI.Analysis.KadisonKastler.SelfAdjointVectorCompactness
import OAI.Analysis.KadisonKastler.SelfAdjointVectorSpace
import OAI.Analysis.KadisonKastler.DenseSupportSeparation

namespace OAI

/-! # The bounded modular Radon--Nikodym equation

The positive-contraction case of the real pairing equation in Rieffel--van
Daele, Pacific Journal of Mathematics 69 (1977), Lemma 4.3, pp.201--202.
Weak compactness and polar support tests construct the solution in the
original represented algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance modularRadonReal : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- A positive commutant contraction has a self-adjoint contractive solution
for every normalized right-half-plane pairing parameter. -/
theorem modular_radon_nikodym_positive (Ω : H) (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (z : ℂ) (hz : z.re = 1) :
    ∃ x : Algebra M, IsSelfAdjoint x ∧ ‖x‖ ≤ 1 ∧
      ∀ a : selfAdjoint (Algebra M),
        (inner ℂ (a.val.val Ω) (b Ω)).re =
          (z * inner ℂ (a.val.val Ω) (x.val Ω)).re := by
  let K := selfAdjointVectorSpace M Ω
  let P : H →L[ℝ] H := K.starProjection.comp ((z • ContinuousLinearMap.id ℂ H).restrictScalars ℝ)
  let C : Set K := {v | (v : H) ∈ selfAdjointVectorImage M Ω P}
  let y : K := K.orthogonalProjectionOnto (b Ω)
  have hclosed : IsClosed C := (selfAdjointVectorImage_closed M Ω P).preimage continuous_subtype_val
  have hconv : Convex ℝ C := (selfAdjointVectorImage_convex M Ω P).linear_preimage K.subtype
  have hbounded : ∀ v ∈ C, ‖v‖ ≤ ‖P‖ * ‖Ω‖ := by
    rintro v ⟨T, hT, he⟩
    change ‖(v : H)‖ ≤ _
    rw [← he]
    have hn : ‖T.toCLM Ω‖ ≤ ‖Ω‖ := by
      calc
        ‖T.toCLM Ω‖ ≤ ‖T.toCLM‖ * ‖Ω‖ := T.toCLM.le_opNorm Ω
        _ ≤ 1 * ‖Ω‖ := mul_le_mul_of_nonneg_right hT.1.2 (norm_nonneg Ω)
        _ = ‖Ω‖ := one_mul _
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg P))
  have htest : ∀ h ∈ Set.range (selfAdjointVectorInSpace M Ω),
      ∃ v ∈ C, inner ℝ h y ≤ inner ℝ h v := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, hu, hun, hle, him⟩ := commutant_positive_polar_support Ω a.val a.property b hb hb0 hb1
    let U := ContinuousLinearMapWOT.ofCLM u.val
    have hU : U ∈ wotSelfAdjointBall M := ⟨⟨u.property, hun⟩, congrArg Subtype.val hu.star_eq⟩
    let v : K := K.orthogonalProjectionOnto (z • u.val Ω)
    refine ⟨v, ⟨U, hU, rfl⟩, ?_⟩
    change inner ℝ (selfAdjointVectorMap M Ω a) (K.starProjection (b Ω)) ≤
      inner ℝ (selfAdjointVectorMap M Ω a) (K.starProjection (z • u.val Ω))
    rw [inner_selfAdjointVector_projection, inner_selfAdjointVector_projection]
    change (inner ℂ (a.val.val Ω) (b Ω)).re ≤ (inner ℂ (a.val.val Ω) (z • u.val Ω)).re
    rw [inner_smul_right, Complex.mul_re, hz, him, one_mul, mul_zero, sub_zero]
    exact hle
  have hy : y ∈ C := mem_closed_convex_of_dense_support hclosed hconv
    (selfAdjointVectorInSpace_dense M Ω) hbounded htest
  obtain ⟨T, hT, hTy⟩ := hy
  let x : Algebra M := ⟨T.toCLM, hT.1.1⟩
  refine ⟨x, ?_, hT.1.2, ?_⟩
  · exact Subtype.ext hT.2.star_eq
  · intro a
    have he := congrArg (fun v : H => inner ℝ (selfAdjointVectorMap M Ω a) v) hTy
    change inner ℝ (selfAdjointVectorMap M Ω a) (K.starProjection (z • x.val Ω)) =
      inner ℝ (selfAdjointVectorMap M Ω a) (K.starProjection (b Ω)) at he
    rw [inner_selfAdjointVector_projection, inner_selfAdjointVector_projection] at he
    simpa only [real_inner_eq_re_inner, RCLike.re_eq_complex_re, selfAdjointVectorMap,
      LinearMap.coe_mk, AddHom.coe_mk, inner_smul_right] using he.symm

end

end KadisonKastler

end OAI
