import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserGridPotential
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedGridError

namespace OAI

/-! The actual equal-mass grid potential and its error against the
manufactured continuous potential, at every evaluation point. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

def gridGaussIndex {ι : Type*} (index : ι → Fin 3 → ℤ)
    (a : ι × (Fin 3 → Fin 2)) : GaussLatticeIndex := (index a.1,a.2)

theorem gridGaussIndex_injective {ι : Type*} (index : ι → Fin 3 → ℤ)
    (hi : Function.Injective index) : Function.Injective (gridGaussIndex index) := by
  intro a b hab
  exact Prod.ext (hi (congrArg (fun z : GaussLatticeIndex => z.1) hab))
    (congrArg (fun z : GaussLatticeIndex => z.2) hab)

def gridNuclearPotential {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) (y : Position) : ℝ :=
  -(rho*h^3/8)*∑ a : ι × (Fin 3 → Fin 2),
    Coulomb.coulombKernel (y-G (gaussLatticePoint h (gridGaussIndex index a)))

theorem gridNuclearPotential_measurable {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) : Measurable (gridNuclearPotential index G rho h) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  exact Coulomb.coulombKernel_measurable.comp (measurable_id.sub measurable_const)

theorem gridNuclearPotential_eq_cells {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) (y : Position) :
    gridNuclearPotential index G rho h y = -rho*(∑ i,
      positionCellGauss (gaussCellCenter h (index i)) h (fun x => Coulomb.coulombKernel (y-G x))) := by
  simp only [gridNuclearPotential,gridGaussIndex,Fintype.sum_prod_type,
    gaussCell_quadrature_lattice,← Finset.mul_sum]
  ring

theorem manufactured_grid_potential_error (hpublished : PublishedC4FlowInput) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (rho H S freq scale : ℝ) (m : ℕ) (u : Fin m → PlanarPosition),
      0 < rho → 0 ≤ H → 1 ≤ S →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ rho/2) →
      tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ (G : Position → ℝ → Position),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
      Function.Bijective (fun x => G x 1) →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k) →
      ∀ (L : ℝ≥0), 0 < L → LipschitzWith L (fun x => G x 1) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S →
      ∀ y : Position,
      |gridNuclearPotential index (fun x => G x 1) rho h y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y)| ≤
      rho*(24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4)+108*Real.pi*(L:ℝ)^2*h^2)+
        (rho*h^3/8)*∑ a : ι × (Fin 3 → Fin 2),
          Coulomb.truncatedCoulomb (6*(L:ℝ)*h) (y-G (gaussLatticePoint h (gridGaussIndex index a)) 1) := by
  obtain ⟨C,hC,hbound⟩ := manufactured_moser_grid_error hpublished
  refine ⟨C,hC,?_⟩
  intro rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD L hL hLip
    ι _ index hindex h hh hh1 hcover y
  have hsub (i : ι) : positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S := by
    rw [← hcover]
    exact Set.subset_iUnion_of_subset i (fun _ hx => hx)
  have he := hbound rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD
    L hL hLip index hindex y h hh hh1 hsub
  have hp := moser_grid_potential hpublished hrho hH (by linarith) hh
    (manufacturedWellField freq scale S u) ((manufacturedWellField_C7 freq scale S u).of_le (by norm_num))
    (manufacturedWellField_compact freq scale (by linarith) u) hcharge hsupp G hflow hbij hfix index hindex hcover y
  rw [gridNuclearPotential_eq_cells,← hp]
  have ha (a b : ℝ) : |-rho*a-(-rho*b)| = rho*|a-b| := by
    rw [show -rho*a-(-rho*b) = -(rho*(a-b)) by ring,abs_neg,abs_mul,abs_of_pos hrho]
  rw [ha]
  apply (mul_le_mul_of_nonneg_left he hrho.le).trans_eq
  simp only [Fintype.sum_prod_type,gridGaussIndex]
  ring

end ContinuumCoulomb

end

end OAI
