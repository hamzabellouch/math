import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CenteredGrid
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserIntegrability

namespace OAI

/-! Exact identification of the continuous part of the finite transported
cubature with the manufactured slab-plus-well potential. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem moser_grid_potential (hpublished : PublishedC4FlowInput)
    {rho H S h : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hh : 0 < h)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    (hcover : (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S)
    (y : Position) :
    -rho*(∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x 1))) = slabPotential rho H S y+V y := by
  have hsub (i : ι) : positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S := by
    rw [← hcover]
    exact Set.subset_iUnion_of_subset i (fun _ hx => hx)
  have hi := moser_coulomb_integrableOn hpublished hrho hH hS V hV hbound hsupport G hG hbij hfix y
  have hsum : (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
      (fun x => Coulomb.coulombKernel (y-G x 1))) =
      ∫ x in slabDomain H S, Coulomb.coulombKernel (y-G x 1) := by
    simp_rw [positionCellIntegral_eq_setIntegral _ hh.le _ (hi.mono_set (hsub _))]
    exact grid_cell_integral_sum_eq index hindex hh hcover _ hi
  have htrans := moser_density_integral hpublished hrho V hV hbound hsupport G hG hbij hfix
    (fun x => Coulomb.coulombKernel (y-x))
  have he : (∫ x in slabDomain H S, synthesizedDensity rho H S V x*Coulomb.coulombKernel (y-x)) =
      ∫ x, Coulomb.coulombKernel (y-x)*synthesizedDensity rho H S V x := by
    calc
      _ = ∫ x in slabDomain H S, Coulomb.coulombKernel (y-x)*synthesizedDensity rho H S V x := by
        apply setIntegral_congr_fun (slabDomain_isClosed H S).measurableSet
        intro x _
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have hv : x ∉ tsupport V := fun h => hx (hsupport h)
        simp only [synthesizedDensity,slabDensity,Set.indicator_of_notMem hx,
          manufacturedCharge_zero hv,add_zero,mul_zero])
  calc
    _ = -(rho*(∫ x in slabDomain H S, Coulomb.coulombKernel (y-G x 1))) := by rw [hsum]; ring
    _ = -(∫ x in slabDomain H S, synthesizedDensity rho H S V x*Coulomb.coulombKernel (y-x)) :=
      congrArg Neg.neg htrans.symm
    _ = -(∫ x, Coulomb.coulombKernel (y-x)*synthesizedDensity rho H S V x) := congrArg Neg.neg he
    _ = _ := synthesizedDensity_potential hrho.le hH hS V (hV.of_le (by norm_num)) hc hbound y

end ContinuumCoulomb

end

end OAI
