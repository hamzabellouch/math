import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ComplementFormLower

namespace OAI

/-! Passing a compressed lower bound and complement estimates to every
antisymmetric weak-H1 state. The mass splitting is exact. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem tensorProjection_interacting_lower {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0)
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (u : Coulomb.H1Vector n) (E a g A K t : ℝ)
    (hg : 0 < g) (hA : 0 ≤ A) (hK : 0 ≤ K) (ht : 0 ≤ t) :
    let p : Coulomb.H1Vector n := finiteTensorProjection (n := n) v hv hL2 hpartial u
    let q : Coulomb.H1Vector n := u.add (Coulomb.H1Vector.scale (-1) p)
    (E+a)*Coulomb.mass p ≤ boundedPotentialForm V p+t*Coulomb.pairEnergy p →
    (E+a+g)*Coulomb.mass q ≤ boundedPotentialForm V q →
    Coulomb.kinetic p ≤ K*Coulomb.mass p →
    (graphBoundedCross (BoundedPotential.operator V hV B hB)
      (h1Coordinates p) (h1Coordinates q))^2 ≤ A*Coulomb.mass p*Coulomb.mass q →
    (E+a-(2*(A+t^2*(8*(n:ℝ)^3*K)))/g)*Coulomb.mass u ≤
      boundedPotentialForm V u+t*Coulomb.pairEnergy u := by
  dsimp only
  intro hfinite hcomp hkin hcross
  have h := interacting_complement_lower V hV B hB
    (finiteTensorProjection v hv hL2 hpartial u)
    (finiteTensorRemainder v hv hL2 hpartial u) E a g A K t
    hg hA hK ht hfinite hcomp hkin hcross
  rw [finiteTensorProjection_add_remainder,
    ← finiteTensorProjection_mass_decomposition v hv hL2 hpartial ho u] at h
  exact h

end ContinuumCoulomb

end

end OAI
