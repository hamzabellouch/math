import OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation
import OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound
import OAI.NumberTheory.PiExponent.Jets.AdmissibleJetPackets
import OAI.NumberTheory.PiExponent.Jets.AdmissibleJetSurjectivity

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleMatrixInterpolation
open AlgebraicGeometry CategoryTheory Filter
open PiExponentSeshadri.Geometry
open DeterminantContradiction AdmissibleBlowupGeometry AdmissibleJetPackets
attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap
  AffineJetCoefficientInterface.Frame AffineJetCoefficientInterface.Sections
  AffineJetCoefficientInterface.coefficient
variable {ν : ℝ} (d : FixedData ν)

theorem eventual_packets_of_eventual_jetRestriction
    (hjet : ∀ᶠ n : ℕ in atTop, Function.Surjective
      (BlowupJetSurjectivity.jetRestriction (centerIdeal d) (hyperplane d) n)) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n) := by
  obtain ⟨N,hN⟩ := WeightedGlobalSectionBound.eventual_admissible_supportBound d
  obtain ⟨e⟩ := actualFrame_exists d
  filter_upwards [hjet, eventually_ge_atTop N] with n hn hnN
  apply packetMap_surjective_of_family d n (sectionPolynomial d n e)
  · intro s
    exact hN n hnN e s
  · exact formalPackets_surjective_of_jetRestriction d n e hn

theorem globalInterpolation_of_eventual_jetRestriction
    (hjet : ∀ ν : ℝ, 2 < ν → ∀ d : FixedData ν,
      ∀ᶠ n : ℕ in atTop, Function.Surjective
        (BlowupJetSurjectivity.jetRestriction (centerIdeal d) (hyperplane d) n)) :
    GlobalInterpolationStatement := by
  apply globalInterpolation_of_eventual_packets
  intro ν hν d
  exact eventual_packets_of_eventual_jetRestriction d (hjet ν hν d)

theorem globalInterpolation : GlobalInterpolationStatement := by
  apply globalInterpolation_of_eventual_jetRestriction
  intro ν _ d
  exact AdmissibleJetSurjectivity.eventually_jetRestriction_surjective d

end PiExponent.AdmissibleMatrixInterpolation

end

end OAI
