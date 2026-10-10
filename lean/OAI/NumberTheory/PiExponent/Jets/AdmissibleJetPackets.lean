import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry
import OAI.NumberTheory.PiExponent.Jets.AffineJetFramedPackets

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleJetPackets
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.AdmissibleBlowupGeometry
open PiExponent.BlowupJetSurjectivity PiExponent.ExceptionalAffineChart
attribute [local irreducible] AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  AdmissibleBlowupGeometry.centerIdeal
  AffineJetCoefficientInterface.Frame AffineJetCoefficientInterface.Sections
  AffineJetCoefficientInterface.coefficient
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

abbrev affineOpen := chartOpen (affineChart d)

def sectionPolynomial (n : ℕ)
    (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d)) :
    AffineJetCoefficientInterface.Sections (hyperplane d) n → PiExponentApprox.FramePolynomial d.m :=
  AffineJetCoefficientInterface.coefficient (affineChart d) (hyperplane d) n e

theorem formalPackets_surjective_of_jetRestriction (n : ℕ)
    (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d))
    (hjet : Function.Surjective (jetRestriction (centerIdeal d) (hyperplane d) n)) :
    Function.Surjective (fun s j =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights (n * (scale d).radius)
        (FormalLogJet.formalJet (d.curveCenters j) (sectionPolynomial d n e s))) := by
  have hc : Function.Injective d.curveCenters := by
    let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
    intro j k h
    exact d.curveCenters_injective i (congrFun h i)
  have he : ∀ i, (scale d).radius ≤ ((scale d).jetPowers i : ℚ) * d.curveJetWeights i := by
    intro i
    rw [mul_comm, (scale d).jetPowers_eq]
  have hs : (((centerIdeal d)^n).support : Set (compactification d)) ⊆
      (affineChart d).opensRange := by
    cases n with
    | zero => simp
    | succ n => simpa using centerIdeal_support_subset_chart d
  exact AffineJetFramedPackets.surjective_of_jetRestriction d.curveCenters hc
    (logCutoff d) (scale d).jetPowers (scale d).jetPowers_pos
    d.curveJetWeights d.curveJetWeights_pos (fun i => (logCutoff_strict d i).le)
    (scale d).radius he n (affineChart d) (centerIdeal d) (hyperplane d) e
    (centerIdeal_restrict d) hs hjet

end PiExponent.AdmissibleJetPackets
end

end OAI
