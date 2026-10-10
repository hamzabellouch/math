import OAI.Analysis.KadisonKastler.CompactHilbertCenter
import OAI.Analysis.KadisonKastler.WOTVectorLowerSemicontinuity
import OAI.Analysis.KadisonKastler.AbelianDerivationAveraging
import OAI.Analysis.FactorGeneration.TraceTopology

namespace OAI

/-! # Geometry of the bounded tracial implementer family -/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Midpoints stay in the weakly compact family of implementers. -/
theorem boundedSelfAdjointImplementers_midpoint (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) {S V : H →WOT[ℂ] H}
    (hS : S ∈ boundedSelfAdjointImplementers M T)
    (hV : V ∈ boundedSelfAdjointImplementers M T) :
    (1 / 2 : ℝ) • (S + V) ∈ boundedSelfAdjointImplementers M T := by
  refine ⟨?_, ?_, ?_⟩
  · change star ((1 / 2 : ℝ) • (S.toCLM + V.toCLM)) = _
    simp only [star_smul, star_trivial, star_add, hS.1.star_eq, hV.1.star_eq]
    rfl
  · change ‖(1 / 2 : ℝ) • (S.toCLM + V.toCLM)‖ ≤ ‖T‖
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hn := norm_add_le S.toCLM V.toCLM
    linarith [hS.2.1, hV.2.1]
  · have he : (1 / 2 : ℝ) • (S.toCLM + V.toCLM) - T =
        (1 / 2 : ℝ) • ((S.toCLM - T) + (V.toCLM - T)) := by module
    change (1 / 2 : ℝ) • (S.toCLM + V.toCLM) - T ∈ M.commutant
    rw [he]
    exact (M.commutant.toStarSubalgebra.restrictScalars ℝ).smul_mem
      (M.commutant.add_mem hS.2.2 hV.2.2) _

/-- Conjugation by a commutant unitary preserves every defining constraint. -/
theorem boundedSelfAdjointImplementers_conjugate (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (u : unitary (H →L[ℂ] H)) (hu : u.val ∈ M.commutant)
    {S : H →L[ℂ] H} (hS : ofCLM S ∈ boundedSelfAdjointImplementers M T) :
    ofCLM (unitaryConj u S) ∈ boundedSelfAdjointImplementers M T := by
  refine ⟨?_, ?_, ?_⟩
  · change star (u.val * S * star u.val) = _
    simp only [star_mul, star_star, hS.1.star_eq, unitaryConj, mul_assoc]
  · simpa only [ofCLM_toCLM, norm_unitaryConj] using hS.2.1
  · have hd := unitaryConj_sub_mem_commutant_of_preserves M T hT u hu
    have hm : unitaryConj u (S - T) ∈ M.commutant :=
      M.commutant.mul_mem (M.commutant.mul_mem hu hS.2.2)
        (M.commutant.toStarSubalgebra.star_mem' hu)
    have he : unitaryConj u S - T =
        unitaryConj u (S - T) + (unitaryConj u T - T) := by
      rw [unitaryConj_sub]
      abel
    change unitaryConj u S - T ∈ M.commutant
    rw [he]
    exact M.commutant.add_mem hm hd

/-- The trace metric on differences is preserved by commutant conjugation. -/
theorem tracial_conjugation_difference_norm
    (N : VonNeumannAlgebra H) (τ : TracialRepresentation N)
    (u : unitary (Algebra N)) (S V : H →L[ℂ] H) (hSV : S - V ∈ N) :
    ‖(unitaryConj (ambientAlgebraUnitary u) S -
        unitaryConj (ambientAlgebraUnitary u) V) τ.vector‖ =
      ‖(S - V) τ.vector‖ := by
  rw [← unitaryConj_sub]
  exact conjugate_norm₂ τ u ⟨S - V, hSV⟩

end

end KadisonKastler

end OAI
