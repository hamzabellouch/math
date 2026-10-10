import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserFlux

namespace OAI

/-! Finite C⁶ regularity of the manufactured well gives the C⁴ transport
field required by the unit-charge cubature. No C∞ assumption is added. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem manufacturedCharge_C4 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiff ℝ 4 (manufacturedCharge V) := by
  have hp (v : Position) : ContDiff ℝ 5 (dirPartial V v) :=
    (hV.fderiv_right (show (5 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const
  have hpp (v : Position) : ContDiff ℝ 4 (dirPartial (dirPartial V v) v) :=
    ((hp v).fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 5 by norm_num)).clm_apply contDiff_const
  have heq : coordinateLaplacian V = fun x =>
      ∑ a : Fin 3, dirPartial (dirPartial V (axis a)) (axis a) x :=
    funext (fun _ => NeutralAtom.coordinateLaplacian_eq_partials
      (hV.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 6)).contDiffAt)
  change ContDiff ℝ 4 (fun x => coordinateLaplacian V x / (4 * Real.pi))
  rw [heq]
  exact (ContDiff.sum (fun a _ => hpp (axis a))).div_const _

def moserDomain (rho : ℝ) (V : Position → ℝ) : Set (ℝ × Position) :=
  {p | homotopyDensity rho V p.1 p.2 ≠ 0}

theorem homotopyDensity_joint_C4 (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiff ℝ 4 (fun p : ℝ × Position => homotopyDensity rho V p.1 p.2) :=
  contDiff_const.add (contDiff_fst.mul ((manufacturedCharge_C4 V hV).comp contDiff_snd))

theorem moserDomain_isOpen (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    IsOpen (moserDomain rho V) :=
  isOpen_ne.preimage (homotopyDensity_joint_C4 rho V hV).continuous

theorem moserVelocity_joint_C4 (rho : ℝ) (V : Position → ℝ) (hV : ContDiff ℝ 6 V) :
    ContDiffOn ℝ 4 (fun p : ℝ × Position => moserVelocity rho V p.1 p.2)
      (moserDomain rho V) := by
  apply (contDiffOn_piLp 2).mpr
  intro a
  have hp : ContDiff ℝ 4 (dirPartial V (axis a)) :=
    ((hV.fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const)
  have hden : ContDiffOn ℝ 4
      (fun p : ℝ × Position => 4 * Real.pi * homotopyDensity rho V p.1 p.2)
      (moserDomain rho V) :=
    (contDiff_const.mul (homotopyDensity_joint_C4 rho V hV)).contDiffOn
  exact (hp.comp contDiff_snd).neg.contDiffOn.div hden (fun p hp =>
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hp)

theorem moserDomain_contains_time_slab {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set Position) ⊆ moserDomain rho V := by
  intro p hp
  exact (homotopyDensity_pos hrho V hbound hp.1.1 hp.1.2 p.2).ne'

/-- Actual spatial C⁴ regularity at each transport time, sufficient for
four differentiated flow equations and fourth-order cubature composition. -/
theorem moserVelocity_C4 {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ContDiff ℝ 4 (moserVelocity rho V t) := by
  apply (contDiff_piLp 2).mpr
  intro a
  have hp : ContDiff ℝ 4 (dirPartial V (axis a)) :=
    ((hV.fderiv_right (show (4 : WithTop ℕ∞) + 1 ≤ 6 by norm_num)).clm_apply contDiff_const)
  have hdensity : ContDiff ℝ 4 (homotopyDensity rho V t) :=
    contDiff_const.add (contDiff_const.mul (manufacturedCharge_C4 V hV))
  exact hp.neg.div (contDiff_const.mul hdensity) (fun x =>
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (homotopyDensity_pos hrho V hbound ht0 ht1 x).ne')

end ContinuumCoulomb

end

end OAI
