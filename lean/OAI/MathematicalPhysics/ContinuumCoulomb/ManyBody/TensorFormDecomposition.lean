import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorProjection
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.RepulsionCross

namespace OAI

/-! Exact form polarization for the full finite tensor projection and its
weak-H1 remainder, including the singular electron repulsion. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem h1_add_sub_cancel {n : ℕ} (u p : Coulomb.H1Vector n) :
    p.add (u.add (Coulomb.H1Vector.scale (-1) p)) = u := by
  cases u
  cases p
  dsimp only [Coulomb.H1Vector.add,Coulomb.H1Vector.scale]
  congr 1
  · funext s x
    ring
  · funext s a x
    ring

theorem finiteTensorProjection_add_remainder {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n) :
    (finiteTensorProjection v hv hL2 hpartial u).add
      (finiteTensorRemainder v hv hL2 hpartial u) = u :=
  h1_add_sub_cancel u _

theorem tensorProjection_form_decomposition {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (u : Coulomb.H1Vector n)
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (t : ℝ) :
    let p := finiteTensorProjection v hv hL2 hpartial u
    let q := finiteTensorRemainder v hv hL2 hpartial u
    boundedPotentialForm V u+t*Coulomb.pairEnergy u =
      (boundedPotentialForm V p+t*Coulomb.pairEnergy p)+
      (boundedPotentialForm V q+t*Coulomb.pairEnergy q)+
      2*(graphBoundedCross (BoundedPotential.operator V hV B hB)
        (h1Coordinates p) (h1Coordinates q)+t*repulsionCross p q) := by
  dsimp only
  have h := boundedPotentialForm_add V hV B hB
    (finiteTensorProjection v hv hL2 hpartial u) (finiteTensorRemainder v hv hL2 hpartial u)
  have hR := pairEnergy_add (finiteTensorProjection v hv hL2 hpartial u)
    (finiteTensorRemainder v hv hL2 hpartial u)
  rw [finiteTensorProjection_add_remainder] at h hR
  rw [h,hR]
  ring

end ContinuumCoulomb

end

end OAI
