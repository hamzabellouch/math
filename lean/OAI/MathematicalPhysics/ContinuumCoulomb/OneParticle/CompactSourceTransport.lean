import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactCoulombJets
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombSourceCubature
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedCoulombDerivative

namespace OAI

/-! Smooth compact orbital densities give a uniform transported-cell bound.
Cells on which the flow is the identity retain the sharper separated-source
bound, so only the compact exceptional region needs the uniform estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem compact_source_transported_cell_bound {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k : ℕ, k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k q x‖ ≤ B)
    (hi : ∀ k : ℕ, k ≤ 4 → (∫ x, ‖iteratedFDeriv ℝ k q x‖) ≤ B)
    (G : Position → Position) (hG : ContDiff ℝ 4 G) {D : ℝ} (_hD : 0 ≤ D)
    (hGD : ∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k)
    (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    |positionCellGauss b h (fun x => NeutralAtom.potentialOf q (G x))-
      positionCellIntegral b h (fun x => NeutralAtom.potentialOf q (G x))| ≤
      24*((2*Real.pi+1)*B)*D^4*h^7 := by
  have hqC := compact_coulomb_C4 hq hc
  apply positionCellGauss_error _ (hqC.comp hG) b hh (by positivity)
  intro x _ y _ z _
  apply fourth_composite_norm_bound (NeutralAtom.potentialOf q) G _ hqC.contDiffAt hG
    (C := (2*Real.pi+1)*B) (D := D) ?_ (hGD _)
  intro k hk
  have ht := compact_coulomb_jet_bound hq hc hk (hb k hk) (G (cubePoint b (h/2) x y z))
  have hL := hi k hk
  nlinarith

private theorem cellGauss_congr_on_cube (b : Position) {h : ℝ} (hh : 0 ≤ h)
    (f g : Position → ℝ) (heq : ∀ x ∈ positionCube b h, f x = g x) :
    positionCellGauss b h f = positionCellGauss b h g := by
  unfold positionCellGauss
  congr 1
  apply gaussTensor3_congr_on
  intro x hx y hy z hz
  exact heq _ (cubePoint_mem_positionCube b hh hx hy hz)

private theorem cellIntegral_congr_on_cube (b : Position) {h : ℝ} (hh : 0 ≤ h)
    (f g : Position → ℝ) (heq : ∀ x ∈ positionCube b h, f x = g x) :
    positionCellIntegral b h f = positionCellIntegral b h g := by
  unfold positionCellIntegral
  congr 1
  apply unitCube_integral_congr
  intro x hx y hy z hz
  exact heq _ (cubePoint_mem_positionCube b hh hx hy hz)

theorem compact_source_unchanged_cell_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : Position → ℝ), ContDiff ℝ 4 q → HasCompactSupport q →
      ∀ (G : Position → Position) (b : Position) (h r : ℝ), 0 ≤ h → 0 < r →
      (∀ x ∈ positionCube b h, G x = x) →
      (∀ x, q x ≠ 0 → ∀ y ∈ positionCube b h, r ≤ ‖y-x‖) →
      |positionCellGauss b h (fun x => NeutralAtom.potentialOf q (G x))-
        positionCellIntegral b h (fun x => NeutralAtom.potentialOf q (G x))| ≤
        (C*h^7/r^5)*(∫ x, ‖q x‖) := by
  obtain ⟨C,hC,hbound⟩ := compact_coulomb_far_cell_error
  refine ⟨C,hC,fun q hq hc G b h r hh hr hfix hsep => ?_⟩
  have heq (x : Position) (hx : x ∈ positionCube b h) :
      NeutralAtom.potentialOf q (G x) = NeutralAtom.potentialOf q x := by rw [hfix x hx]
  rw [cellGauss_congr_on_cube b hh _ _ heq,cellIntegral_congr_on_cube b hh _ _ heq]
  exact hbound q hq hc b h r hh hr hsep

end ContinuumCoulomb

end

end OAI
