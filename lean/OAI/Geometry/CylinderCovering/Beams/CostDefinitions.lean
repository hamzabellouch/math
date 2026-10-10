import Mathlib

namespace OAI

noncomputable section
namespace CylinderCovering.BeamCost

def S (p : ℝ) : ℝ := p^2+(1-p)^2
def T (p : ℝ) : ℝ := p^4+(1-p)^4

def beamDensity (a p : ℝ) : ℝ :=
  1 / Real.sqrt (1-a*(2-a)*S p/2+a^2*(2-a)^2*T p/4)

def beamCost (a : ℝ) : ℝ := (2-a)^2 * ∫ p in (0:ℝ)..1, beamDensity a p

def stripWidth (a t : ℝ) : ℝ :=
  max (a*(1-2*t^2)+a^2*t^2*(1+(1-|t|)^2+t^2)+25*a^3) 0

def stripDensity (a t : ℝ) : ℝ :=
  stripWidth a t / Real.sqrt (1+(a*t-a^2*t^3)^2)

def stripCost (a : ℝ) : ℝ :=
  2*Real.sqrt 2 * ∫ t in (-1:ℝ)..1, stripDensity a t

def stripPolynomial (a t : ℝ) : ℝ :=
  a*(1-2*t^2)+a^2*t^2*(1+(1-t)^2+t^2)

def cutoff : ℝ := Real.sqrt 2/2

def CostStatement : Prop :=
  (∀ a : ℝ, 0 ≤ a → a ≤ 1/4 →
    |beamCost a-(4-(8/3)*a-(11/10)*a^2)| ≤ 300*a^3) ∧
  (∀ a : ℝ, 0 ≤ a → a ≤ 1/100 →
    |stripCost a-((8/3)*a+((26/15)-Real.sqrt 2/2)*a^2)| ≤ 300*a^3) ∧
  (∀ a : ℝ, 0 ≤ a → a ≤ 1/100 →
    |beamCost a+stripCost a-(4+((19/30)-Real.sqrt 2/2)*a^2)| ≤ 600*a^3) ∧
  (∀ a : ℝ, 0 < a → a ≤ 1/20000 → beamCost a+stripCost a < 4)

end CylinderCovering.BeamCost

end

end OAI
