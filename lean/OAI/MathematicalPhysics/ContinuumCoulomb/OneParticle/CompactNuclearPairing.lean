import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactSourcePairing
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabRegularity

namespace OAI

/-! Identification of the compact-source cubature error with the actual
nuclear matrix element, including the manufactured continuous potential. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem gridNuclearPotential_mul_integrable {q : Position → ℝ}
    (hq : Continuous q) (hc : HasCompactSupport q)
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho h : ℝ) :
    Integrable (fun y => gridNuclearPotential index G rho h y*q y) := by
  have hi (a : ι × (Fin 3 → Fin 2)) : Integrable (fun y =>
      Coulomb.coulombKernel (y-G (gaussLatticePoint h (gridGaussIndex index a)))*q y) := by
    convert compact_coulomb_eval_integrable hq hc (G (gaussLatticePoint h (gridGaussIndex index a))) using 1
    funext y
    ring
  convert (integrable_finsetSum Finset.univ (fun a _ => hi a)).const_mul (-(rho*h^3/8)) using 1
  funext y
  simp only [gridNuclearPotential,Finset.sum_mul,mul_assoc]

theorem manufactured_compact_nuclear_pairing (hpublished : PublishedC4FlowInput)
    {rho H S h : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hh : 0 < h)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hcV : HasCompactSupport V)
    (hcharge : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hflow : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (hG : Continuous (fun x => G x 1))
    {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    (hcover : (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S)
    {q : Position → ℝ} (hq : ContDiff ℝ 4 q) (hcq : HasCompactSupport q)
    (hpos : ∀ y, 0 ≤ q y) :
    (∫ y, (gridNuclearPotential index (fun x => G x 1) rho h y-
        (slabPotential rho H S y+V y))*q y) =
      -rho*((∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => NeutralAtom.potentialOf q (G x 1)))-
        ∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
        (fun x => NeutralAtom.potentialOf q (G x 1))) := by
  have hsub (i : ι) : positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S := by
    rw [← hcover]
    exact Set.subset_iUnion_of_subset i (fun _ hx => hx)
  have hkernel (y : Position) := moser_coulomb_integrableOn hpublished hrho hH hS
    V hV hcharge hsupport G hflow hbij hfix y
  have hsum (f : Position → ℝ) (hf : IntegrableOn f (slabDomain H S)) :
      (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h f) =
        ∫ x in slabDomain H S, f x := by
    simp_rw [positionCellIntegral_eq_setIntegral _ hh.le _ (hf.mono_set (hsub _))]
    exact grid_cell_integral_sum_eq index hindex hh hcover f hf
  have hpoint (y : Position) :
      -rho*(∫ x in slabDomain H S, Coulomb.coulombKernel (y-G x 1)) = slabPotential rho H S y+V y := by
    rw [← hsum _ (hkernel y)]
    exact moser_grid_potential hpublished hrho hH hS hh V hV hcV hcharge hsupport
      G hflow hbij hfix index hindex hcover y
  have hiPot : IntegrableOn (fun x => NeutralAtom.potentialOf q (G x 1)) (slabDomain H S) :=
    ((compact_coulomb_C4 hq hcq).continuous.comp hG).continuousOn.integrableOn_compact
      (slabDomain_isCompact hH hS)
  have hcontinuous : (∫ y, (slabPotential rho H S y+V y)*q y) =
      -rho*(∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
        (fun x => NeutralAtom.potentialOf q (G x 1))) := by
    rw [hsum _ hiPot,compact_source_transport_pairing hq hcq hpos (slabDomain_isCompact hH hS) hG,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← hpoint y]
    ring
  have hPi : Integrable (fun y => (slabPotential rho H S y+V y)*q y) :=
    (((slabPotential_continuous hrho.le hH hS).add hV.continuous).mul hq.continuous).integrable_of_hasCompactSupport
      hcq.mul_left
  simp_rw [sub_mul]
  rw [integral_sub (gridNuclearPotential_mul_integrable hq.continuous hcq index (fun x => G x 1) rho h) hPi,
    gridNuclearPotential_pairing hq.continuous hcq,hcontinuous]
  ring

end ContinuumCoulomb

end

end OAI
