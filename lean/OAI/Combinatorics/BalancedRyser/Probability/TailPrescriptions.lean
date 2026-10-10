import OAI.Combinatorics.BalancedRyser.Probability.TailConditioning

namespace OAI

namespace Balanced.TailConditioning

universe u v w
variable {I : Type u} (Q : I → Type v) {V : Type w}

def ambientCylinder (embed : ∀ i, Q i → V) (J : Finset I) (a : I → V) :
    Set (Slots.Assignment Q) :=
  {ω | ∀ i ∈ J, embed i (ω i) = a i}

noncomputable def conditionalAmbientCylinder [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)] (G : SimpleGraph (Sigma Q))
    (embed : ∀ i, Q i → V) (J : Finset I) (a : I → V) : ℝ :=
  (Slots.law Q).real (ambientCylinder Q embed J a ∩ independentTransversals Q G) /
    (Slots.law Q).real (independentTransversals Q G)

end Balanced.TailConditioning

end OAI
