import OAI.Analysis.KadisonKastler.SelfAdjointPolarTest

namespace OAI

/-! # A support inequality for positive commutant contractions

This is the operator-order part of the bounded modular Radon--Nikodym
argument. The sign of a self-adjoint test operator dominates its pairing
with a positive contraction from the commutant.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance commutantSupportOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance commutantSupportPreorder : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance commutantSupportLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance commutantSupportStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem commutant_positive_polar_support (Ω : H) (x : Algebra M)
    (hx : IsSelfAdjoint x) (b : H →L[ℂ] H) (hb : b ∈ M.commutant)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ u : Algebra M, IsSelfAdjoint u ∧ ‖u‖ ≤ 1 ∧
      (inner ℂ (x.val Ω) (b Ω)).re ≤ (inner ℂ (x.val Ω) (u.val Ω)).re ∧
      (inner ℂ (x.val Ω) (u.val Ω)).im = 0 := by
  obtain ⟨u, hu, hun, _, hxu⟩ := selfAdjoint_polar_test x hx
  let P : H →L[ℂ] H := (x⁺).val
  let N : H →L[ℂ] H := (x⁻).val
  have hP : 0 ≤ P := by
    have h := map_rel M.toStarSubalgebra.subtype (CFC.posPart_nonneg x)
    change M.toStarSubalgebra.subtype 0 ≤ P at h
    simpa only [map_zero] using h
  have hN : 0 ≤ N := by
    have h := map_rel M.toStarSubalgebra.subtype (CFC.negPart_nonneg x)
    change M.toStarSubalgebra.subtype 0 ≤ N at h
    simpa only [map_zero] using h
  have hPb : Commute P b := hb _ (Set.mem_union_left _ (x⁺).property)
  have hNb : Commute N b := hb _ (Set.mem_union_left _ (x⁻).property)
  have hp : 0 ≤ P * (1 - b) :=
    Commute.mul_nonneg hP (sub_nonneg.mpr hb1) ((Commute.one_right P).sub_right hPb)
  have hn : 0 ≤ N * (1 + b) :=
    Commute.mul_nonneg hN (add_nonneg zero_le_one hb0) ((Commute.one_right N).add_right hNb)
  have hparts : x.val = P - N :=
    congrArg Subtype.val (CFC.posPart_sub_negPart x hx).symm
  have he : P + N - x.val * b = P * (1 - b) + N * (1 + b) := by
    rw [hparts]
    noncomm_ring
  have hpos : 0 ≤ P + N - x.val * b := by rw [he]; exact add_nonneg hp hn
  have hxu' : x.val * u.val = P + N := congrArg Subtype.val hxu
  have hsa : x.val.adjoint = x.val :=
    (show IsSelfAdjoint x.val from congrArg Subtype.val hx.star_eq).star_eq
  have hi (A : H →L[ℂ] H) : inner ℂ (x.val Ω) (A Ω) = inner ℂ Ω ((x.val * A) Ω) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hsa]
    rfl
  refine ⟨u, hu, hun, ?_, ?_⟩
  · have h := (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).re_inner_nonneg_right Ω
    change 0 ≤ (inner ℂ Ω ((P + N - x.val * b) Ω)).re at h
    simp only [sub_apply, inner_sub_right, Complex.sub_re] at h
    rw [hi b, hi u.val, hxu']
    linarith
  · rw [hi u.val, hxu']
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (add_nonneg hP hN)).toLinearMap.isSymmetric.im_inner_self_apply Ω

end

end KadisonKastler

end OAI
