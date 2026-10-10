import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedFarQuadrature
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserFlowRegularity

namespace OAI

/-! The far part of the actual manufactured nuclear quadrature. Its error
has no factor depending on the horizontal area of the enclosing slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb

theorem manufactured_moser_far_grid_error (hpublished : PublishedC4FlowInput) :
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
      ∀ (y : Position) (h : ℝ), 0 < h → h ≤ 1 →
      (∀ i, positionCube (gaussCellCenter h (index i)) h ⊆ slabDomain H S) →
      (∀ i, 4*(L:ℝ)*h ≤ ‖y-G (gaussCellCenter h (index i)) 1‖) →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
        (fun x => Coulomb.coulombKernel (y-G x 1)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => Coulomb.coulombKernel (y-G x 1)))| ≤
        24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4) := by
  obtain ⟨C,hC,hbound⟩ := transportedCoulomb_far_grid_hybrid_error
  refine ⟨C,hC,?_⟩
  intro rho H S freq scale m u hrho hH hS hcharge hsupp G hflow hbij hfix D hD hGD L hL hLip
    ι _ index hindex y h hh hh1 hsub hfar
  let V := manufacturedWellField freq scale S u
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 freq scale S u).of_le (by norm_num)
  have hGreg : ContDiff ℝ 4 (fun x => G x 1) :=
    (moser_flow_C4 hpublished hrho V hV hcharge G hflow).1 1 ⟨by norm_num,le_rfl⟩
  have he := hbound (fun x => G x 1) hGreg (tsupport V) (isClosed_tsupport V) hfix
    D hD hGD L hL hLip index y h hh hfar
  have ht := moser_inverseFifth_grid_sum_bound hpublished hrho hH (by linarith) V hV hcharge hsupp
    G hflow hbij hfix hL hLip index hindex hh hsub y hfar
  have hc := manufactured_cellHits_volume_bound index hindex hh hh1 hS freq scale u
  have hs : 32*(∑ i, h^3/‖y-G (gaussCellCenter h (index i)) 1‖^5)+
      (∑ i, cellHits (tsupport V) (gaussCellCenter h (index i)) h*h^3) ≤
      3072*Real.pi/((L:ℝ)*h)^2+216*m*S := by
    have hi := add_le_add (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 32)) hc
    convert hi using 1
    ring
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 24*C*D^4*h^4)).trans_eq
  have hLn : (L:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hL)
  field_simp [hh.ne',hLn]

end ContinuumCoulomb

end

end OAI
