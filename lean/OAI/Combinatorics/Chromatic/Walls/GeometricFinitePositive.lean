import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.InputProduct
import OAI.Combinatorics.Chromatic.Walls.FiniteWallPositive
import OAI.Combinatorics.Chromatic.Walls.WeightedInverseAdjoint

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀p,Ω p p=0)
variable (p : I → M) (κ : I → ℤ) (ε : I → Bool)
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable (c η : I → ℝ) (hc : ∀i,0<c i) (t : ℝ)
variable (hp : ∀i j,(Ω (p i) (p j):ℝ)=t*(η i*c j-c i*η j))
variable (l : List I) (hn : l.Nodup) (hall : l.toFinset=Finset.univ)
variable (hl : l.Pairwise (fun i j=>0≤Ω (p i) (p j)))
variable (h : M →+ ℝ) (θ : ℝ) (hh : ∀d,h (rootSum p d)=slopeValue c η θ d)
variable (m : M)

include hΩ hc hp hn hall hl hh in
lemma geometric_zero_adjoint_positive
    (hm : ∀d∈slopeDimensions c η hc θ,0≤Ω (rootSum p d) m) :
    let F := PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
      (zeroProject LaurentRay.vUnit Ω h)
      ((l.map (literalAxis κ ε Ω (rootSum p) w)).prod)
    IntegralPositive Ω (F*C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1) := by
  let a:=geometricQuiver Ω p ε
  let : Fact (∀θ,SlopeEulerSymmetric a c η θ) :=
    ⟨geometricQuiver_symmetric Ω p ε hΩ c η hc t hp⟩
  have H:=literalInput_ordered a κ ε Ω (rootSum p) w
    (geometricQuiver_euler Ω p ε hΩ) l hn hall
    (geometricQuiver_pairwise Ω p ε hΩ l hn hl)
  dsimp only
  rw [←H]
  exact finiteInput_zero_adjoint_positive a κ c η hc w Ω (rootSum p)
    hΩ (geometricQuiver_euler Ω p ε hΩ) θ m hm h hh ε
    (geometricQuiver_diag Ω p ε)

include hΩ hc hp hn hall hl hh in
lemma geometric_zero_inverse_adjoint_positive
    (hm : ∀d∈slopeDimensions c η hc θ,Ω (rootSum p d) m≤0) :
    let F := PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
      (zeroProject LaurentRay.vUnit Ω h)
      ((l.map (literalAxis κ ε Ω (rootSum p) w)).prod)
    IntegralPositive Ω (invOfUnit F 1*C (Torus.X LaurentRay.vUnit Ω m)*F) := by
  let a:=geometricQuiver Ω p ε
  let : Fact (∀θ,SlopeEulerSymmetric a c η θ) :=
    ⟨geometricQuiver_symmetric Ω p ε hΩ c η hc t hp⟩
  have H:=literalInput_ordered a κ ε Ω (rootSum p) w
    (geometricQuiver_euler Ω p ε hΩ) l hn hall
    (geometricQuiver_pairwise Ω p ε hΩ l hn hl)
  dsimp only
  rw [←H]
  exact finiteInput_zero_inverse_adjoint_positive a κ c η hc w Ω (rootSum p)
    hΩ (geometricQuiver_euler Ω p ε hΩ) θ m hm h hh ε
    (geometricQuiver_diag Ω p ε)
end
end ElementaryPositivity.RawShuffle

end

end OAI
