import OAI.Analysis.KadisonKastler.ConstructedFiniteAmplification
import OAI.Analysis.KadisonKastler.CompleteCommutantDistance
import OAI.Analysis.KadisonKastler.ProbabilityOperatorRelations

namespace OAI

/-! # Quantitative commutant approximation for nearby finite factors

The constructed finite-factor estimate and the proved complete
commutator-distance formula give the approximation needed to align
reducing projections. No published perturbation input is used.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

local instance finiteFactorCommutantNearOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance finiteFactorCommutantNearStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

omit [TopologicalSpace.SeparableSpace H] in
theorem concreteDerivation_norm_le_of_commutant_near
    (M N : VonNeumannAlgebra H) {γ : ℝ} (hγ : 0 < γ)
    (hgap : kkDistance M N < γ) (T : H →L[ℂ] H)
    (hT : T ∈ N.commutant) (hTnorm : ‖T‖ ≤ 1) :
    ‖concreteDerivation M T‖ ≤ 2 * γ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro a ha
  obtain ⟨b, hb, hab⟩ := exists_unitBall_approx (M := M) (N := N)
    ⟨a.property, ha.le⟩ hgap
  have hcomm : b * T = T * b := VonNeumannAlgebra.mem_commutant_iff.mp hT b hb.1
  have hn := norm_commutator_of_near_commuting a.val b T hab.le hcomm
  change ‖T * a.val - a.val * T‖ ≤ 2 * γ
  rw [norm_sub_rev]
  exact hn.trans (mul_le_of_le_one_right (by positivity) hTnorm)

theorem finiteFactor_commutant_approx_of_gap
    (M N : VonNeumannAlgebra H) (hM : Generator.IsII1Factor M.toStarSubalgebra)
    {γ : ℝ} (hγ : 0 < γ) (hgap : kkDistance M N < γ)
    (T : H →L[ℂ] H) (hT : T ∈ N.commutant) (hTnorm : ‖T‖ ≤ 1) :
    ∃ D ∈ M.commutant, ‖D - T‖ < 2000000 * γ := by
  have hn := concreteDerivation_norm_le_of_commutant_near M N hγ hgap T hT hTnorm
  have hb (a : H →L[ℂ] H) (ha : a ∈ M) :
      ‖T * a - a * T‖ ≤ (2 * γ) * ‖a‖ := by
    exact ((concreteDerivation M T).le_opNorm ⟨a, ha⟩).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg a))
  have hcb := constructed_finiteFactor_completelyBounded M hM T (by positivity) hb
  obtain ⟨D, hD, hd⟩ := exists_commutant_of_completelyBounded M.toStarSubalgebra.subtype T
    (by positivity : 0 ≤ 1000000 * (2 * γ)) hcb
    (r := 2000000 * γ) (by nlinarith)
  refine ⟨D, VonNeumannAlgebra.mem_commutant_iff.mpr ?_, hd⟩
  intro a ha
  exact (hD ⟨a, ha⟩).symm

end

end KadisonKastler

end OAI
