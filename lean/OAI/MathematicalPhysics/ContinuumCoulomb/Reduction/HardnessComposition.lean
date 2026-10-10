import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.TM2Composition

namespace OAI

/-! Promise-hardness transport through actual polynomial-time machine
composition, with both yes and no promise maps retained. -/

noncomputable section
namespace ContinuumCoulomb
open BinaryEncoding

def PolynomialManyOne.comp {α β γ : Type}
    {ea : α → BitString} {eb : β → BitString} {ec : γ → BitString}
    {P : PromiseProblem α} {Q : PromiseProblem β} {R : PromiseProblem γ}
    (F : PolynomialManyOne ea eb P Q) (G : PolynomialManyOne eb ec Q R) :
    PolynomialManyOne ea ec P R where
  map := G.map ∘ F.map
  polynomialTime := TM2Composition.computable (f := F.map) (g := G.map) F.polynomialTime G.polynomialTime
  maps_yes x hx := G.maps_yes (F.map x) (F.maps_yes x hx)
  maps_no x hx := G.maps_no (F.map x) (F.maps_no x hx)

theorem QMAHard.of_reduction {α β : Type}
    {ea : α → BitString} {eb : β → BitString}
    {P : PromiseProblem α} {Q : PromiseProblem β}
    (hP : QMAHard ea P) (F : PolynomialManyOne ea eb P Q) : QMAHard eb Q := by
  intro R hR
  rcases hP R hR with ⟨G⟩
  exact ⟨G.comp F⟩

end ContinuumCoulomb

end

end OAI
