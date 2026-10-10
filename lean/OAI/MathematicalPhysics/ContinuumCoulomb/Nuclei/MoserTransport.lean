import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserJacobian
import Mathlib.MeasureTheory.Function.Jacobian

namespace OAI

/-! Exact change of variables from uniform slab density to the actual
manufactured density. The identity is for arbitrary scalar integrands,
including the Coulomb kernel used by the nuclear cubature. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem moser_flowJacobian_pos (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (x : Position) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < flowJacobian G t x := by
  have he := moser_density_jacobian hpublished hrho V hV hbound G hG x ht
  have hp : 0 < homotopyDensity rho V t (G x t) :=
    homotopyDensity_pos hrho V hbound ht.1 ht.2 _
  have hm : 0 < homotopyDensity rho V t (G x t) * flowJacobian G t x := by
    rw [he]
    exact hrho
  rcases mul_pos_iff.mp hm with h | h
  · exact h.2
  · exact False.elim (not_lt_of_ge hp.le h.1)

/-- The actual Moser map pushes uniform density to the synthesized
nonnegative nuclear density, with the entire slab preserved. -/
theorem moser_density_integral (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (f : Position → ℝ) :
    (∫ y in slabDomain H S, synthesizedDensity rho H S V y * f y) =
      rho * ∫ x in slabDomain H S, f (G x 1) := by
  have hs := (slabDomain_isClosed H S).measurableSet
  have h1 : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, le_rfl⟩
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hG).1 1 h1
  have himage := moser_time_one_preserves_slab V hsupport (fun x => G x 1) hbij hfix
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun x (_hx : x ∈ slabDomain H S) =>
      (hreg.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
    hbij.1.injOn (fun y => synthesizedDensity rho H S V y * f y)
  rw [himage] at hchange
  rw [hchange, ← integral_const_mul]
  apply setIntegral_congr_fun hs
  intro x hx
  have hGx : G x 1 ∈ slabDomain H S := by
    rw [← himage]
    exact ⟨x, hx, rfl⟩
  have hJ := moser_density_jacobian hpublished hrho V hV hbound G hG x h1
  have hp := moser_flowJacobian_pos hpublished hrho V hV hbound G hG x h1
  change |flowJacobian G 1 x| * (synthesizedDensity rho H S V (G x 1) * f (G x 1)) = _
  rw [abs_of_pos hp]
  simp only [synthesizedDensity, slabDensity, Set.indicator_of_mem hGx] at hJ ⊢
  simp only [homotopyDensity, one_mul] at hJ
  calc
    flowJacobian G 1 x * ((rho + manufacturedCharge V (G x 1)) * f (G x 1)) =
      ((rho + manufacturedCharge V (G x 1)) * flowJacobian G 1 x) * f (G x 1) := by ring
    _ = rho * f (G x 1) := by rw [hJ]

end ContinuumCoulomb

end

end OAI
