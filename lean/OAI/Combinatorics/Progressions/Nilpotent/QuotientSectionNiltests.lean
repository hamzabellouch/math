import OAI.Combinatorics.Progressions.Estimates.PositiveReconstruction
import OAI.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_quotient_section_niltests {L Z σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d n : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))] [PseudoMetricSpace Z]
    (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (v : Q.Space × Z → ℂ) {K : ℝ≥0}
    (hv : letI := Q.metricSpace; LipschitzWith K v)
    (hpositive : ∀ y, (v y).im = 0 ∧ 0 ≤ (v y).re ∧ (v y).re ≤ 1)
    {b : ℝ} (hb : 0 ≤ b) (hgeom : Q.GeometryComplexityLE b) (hK : (K : ℝ) ≤ Real.exp b) :
    ∃ tests : Z → Q.Niltest w,
      (∀ z, (tests z).UnitIntervalValued) ∧
      (∀ z, (tests z).ComplexityLE (b + 2)) ∧
      ∀ z x, (tests z).eval x =
        v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
          (D.filtration.realification.polynomialOrbitEval w x g)), z) := by
  let q₀ := D.filtration.realQuotientPolynomialOrbit (D.filtration.layerIdeal (s + 1))
    (t := s) le_rfl g
  have hadapted : Q.filtration.realification.Adapted w q₀.log := by
    rw [hQ]
    exact q₀.adapted
  let q : Q.filtration.realification.PolynomialOrbit w :=
    NilpotentLieFiltration.polynomialOrbitOfLog q₀.log hadapted
  let := Q.metricSpace
  let tests : Z → Q.Niltest w := fun z => {
    orbit := q
    observable := fun y => v (y, z)
    normBound := 1
    lipBound := K
    norm_le := fun y => by
      simpa only [positiveClip_eq_self _ (hpositive (y, z)), NNReal.coe_one] using
        norm_positiveClip_le_one (v (y, z))
    lipschitz := by
      simpa only [mul_one, Function.comp_def] using hv.comp (LipschitzWith.prodMk_right z) }
  have hlog : Real.log (3 + (K : ℝ)) ≤ b + 2 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 : 1 ≤ Real.exp b := Real.one_le_exp hb
    have h2 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg b)]
  refine ⟨tests, fun z y => hpositive (y, z), ?_, ?_⟩
  · intro z
    refine ⟨hgeom.mono Q (by linarith), ?_⟩
    change Real.log (2 + 1 + (K : ℝ)) ≤ b + 2
    norm_num only [show (2 : ℝ) + 1 = 3 by norm_num]
    exact hlog
  · intro z x
    have heval := D.filtration.realQuotientPolynomialOrbit_eval
      (D.filtration.layerIdeal (s + 1)) (t := s) le_rfl g x
    exact congrArg (fun y : Q.RealGroup => v (QuotientGroup.mk y, z)) heval

end Erdos3.RationalFilteredNilmanifold

end

end OAI
