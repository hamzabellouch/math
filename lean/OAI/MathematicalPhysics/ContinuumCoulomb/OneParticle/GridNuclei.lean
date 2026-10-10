import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearGridPotential
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedNodes
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ShiftedPhysicalForm

namespace OAI

/-! The transported Gauss cloud is an actual collection of distinct unit
nuclei. Its physical form has exactly the slab-origin energy offset. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

private theorem gaussLatticePoint_injective {h : ℝ} (hh : 0 < h) :
    Function.Injective (gaussLatticePoint h) := by
  intro a b hab
  by_contra hne
  have hs := gaussLatticePoint_separation hh a b hne
  rw [hab,sub_self,norm_zero] at hs
  linarith

def gridNuclei {ι : Type*} [Fintype ι] [Nonempty ι] (index : ι → Fin 3 → ℤ)
    (hi : Function.Injective index) (G : Position → Position) (hG : Function.Injective G)
    {h : ℝ} (hh : 0 < h) : Coulomb.Nuclei (Fintype.card (ι × (Fin 3 → Fin 2))) where
  nonempty := Fintype.card_pos
  position a := G (gaussLatticePoint h
    (gridGaussIndex index ((Fintype.equivFin (ι × (Fin 3 → Fin 2))).symm a)))
  distinct := (hG.comp ((gaussLatticePoint_injective hh).comp
    (gridGaussIndex_injective index hi))).comp (Fintype.equivFin _).symm.injective
  charge _ := 1
  charge_ge_one _ := le_rfl

theorem gridNuclei_attraction {ι : Type*} [Fintype ι] [Nonempty ι]
    (index : ι → Fin 3 → ℤ) (hi : Function.Injective index)
    (G : Position → Position) (hG : Function.Injective G) {h : ℝ} (hh : 0 < h) (y : Position) :
    Coulomb.attraction (gridNuclei index hi G hG hh) y =
      ∑ a : ι × (Fin 3 → Fin 2),
        Coulomb.coulombKernel (y-G (gaussLatticePoint h (gridGaussIndex index a))) := by
  simp only [Coulomb.attraction,gridNuclei,one_mul]
  exact (Fintype.equivFin (ι × (Fin 3 → Fin 2))).symm.sum_comp
    (fun a : ι × (Fin 3 → Fin 2) =>
      Coulomb.coulombKernel (y-G (gaussLatticePoint h (gridGaussIndex index a))))

theorem gridNuclearPotential_attraction {ι : Type*} [Fintype ι] [Nonempty ι]
    (index : ι → Fin 3 → ℤ) (hi : Function.Injective index)
    (G : Position → Position) (hG : Function.Injective G) {h : ℝ} (hh : 0 < h)
    (rho : ℝ) (y : Position) :
    gridNuclearPotential index G rho h y =
      -(rho*h^3/8)*Coulomb.attraction (gridNuclei index hi G hG hh) y := by
  rw [gridNuclei_attraction]
  rfl

theorem manufactured_grid_split {ι : Type*} [Fintype ι] [Nonempty ι]
    (index : ι → Fin 3 → ℤ) (hi : Function.Injective index)
    (G : Position → Position) (hG : Function.Injective G) {h : ℝ} (hh : 0 < h)
    (rho H S freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hscale : rho*h^3/8=scale⁻¹) (y : Position) :
    manufacturedSlabPotential rho H S freq scale u y+
      (gridNuclearPotential index G rho h y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y)) =
      -scale⁻¹*Coulomb.attraction (gridNuclei index hi G hG hh) y-slabPotential rho H S 0 := by
  rw [gridNuclearPotential_attraction index hi G hG hh, hscale]
  unfold manufacturedSlabPotential
  ring

end ContinuumCoulomb

end

end OAI
