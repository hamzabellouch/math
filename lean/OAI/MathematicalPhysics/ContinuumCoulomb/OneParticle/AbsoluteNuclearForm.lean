import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearGridPotential
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.WeightedPotentialBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabRegularity

namespace OAI

/-! Absolute-value form bound for unit-nucleus replacement. It holds
for every spin component of every many-electron weak-H1 state. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem manufactured_grid_absolute_form_error (hpublished : PublishedC4FlowInput)
    (L K : ℝ≥0) (hL : 0 < L) (hK : 0 < K) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
    ∀ (rho H S freq scale : ℝ) (m : ℕ) (u : Fin m → PlanarPosition),
      0 < rho → 0 ≤ H → 1 ≤ S →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ rho/2) →
      tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ (G : Position → ℝ → Position),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
      Function.Bijective (fun x => G x 1) →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k) →
      LipschitzWith L (fun x => G x 1) → AntilipschitzWith K (fun x => G x 1) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S →
      ∀ (n : ℕ) (w : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n),
      Integrable (fun x => |gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
        (slabPotential rho H S (Coulomb.position x i)+
          manufacturedWellField freq scale S u (Coulomb.position x i))| * ‖w.value s x‖^2) ∧
      (∫ x, |gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
        (slabPotential rho H S (Coulomb.position x i)+
          manufacturedWellField freq scale S u (Coulomb.position x i))| *‖w.value s x‖^2) ≤
      rho*(24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4)+108*Real.pi*(L:ℝ)^2*h^2)*
        (∫ x, ‖w.value s x‖^2)+
      rho*A*h^2*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2) := by
  obtain ⟨C,hC,hpoint⟩ := manufactured_grid_potential_error hpublished
  have hκ : 0 < 6*(L:ℝ) := by positivity
  obtain ⟨A,hA,hnear⟩ := transportedGauss_truncated_form hκ K hK
  refine ⟨C,A,hC,hA,?_⟩
  intro rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD hLip hAnti
    ι _ index hindex h hh hh1 hcover n w s i
  let F : Position → ℝ := fun y => gridNuclearPotential index (fun x => G x 1) rho h y-
    (slabPotential rho H S y+manufacturedWellField freq scale S u y)
  let B := rho*(24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4)+108*Real.pi*(L:ℝ)^2*h^2)
  let R : ι × (Fin 3 → Fin 2) → Position := fun a => G (gaussLatticePoint h (gridGaussIndex index a)) 1
  have hF : Measurable F := (gridNuclearPotential_measurable index (fun x => G x 1) rho h).sub
    (((slabPotential_continuous hrho.le hH (by linarith)).add
      (manufacturedWellField_C7 freq scale S u).continuous).measurable)
  have he := weighted_potential_absolute_bound w s i F hF R (6*(L:ℝ)*h) B (rho*h^3/8)
    (hpoint rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix
      D hD hGD L hL hLip index hindex h hh hh1 hcover)
  have hn := hnear n w s i h rho hh hh1 hrho.le (gridGaussIndex index)
    (gridGaussIndex_injective index hindex) (fun x => G x 1) hAnti
  exact ⟨he.1, he.2.trans (add_le_add le_rfl hn)⟩

end ContinuumCoulomb

end

end OAI
