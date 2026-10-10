import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model
import OAI.Analysis.CoulombRadii.FormDomain.SmoothCompact

namespace OAI

/-! A concrete normalized weak-H¹ trial, independent of all nuclear data. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def oneElectronBump : ContDiffBump (0 : Configuration 1) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def oneElectronBumpState : Coulomb.H1Vector 1 :=
  Coulomb.H1Vector.ofSmoothCompact
    (fun _ x => (oneElectronBump x : ℂ))
    (fun _ => Complex.ofRealCLM.contDiff.comp oneElectronBump.contDiff)
    (fun _ => oneElectronBump.hasCompactSupport.comp_left Complex.ofReal_zero)

theorem oneElectronBumpState_mass_pos : 0 < Coulomb.mass oneElectronBumpState := by
  have hzero : (fun t : ℝ => t ^ 2) 0 = 0 := zero_pow (by decide)
  have hc : HasCompactSupport (fun x : Configuration 1 => oneElectronBump x ^ 2) :=
    oneElectronBump.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) hzero
  have hI : Integrable (fun x : Configuration 1 => oneElectronBump x ^ 2) :=
    (oneElectronBump.continuous.pow 2).integrable_of_hasCompactSupport hc
  have hb0 : oneElectronBump (0 : Configuration 1) = 1 :=
    oneElectronBump.one_of_mem_closedBall (by simp [oneElectronBump])
  have hpos : 0 < ∫ x : Configuration 1, oneElectronBump x ^ 2 :=
    integral_pos_of_integrable_nonneg_nonzero (oneElectronBump.continuous.pow 2)
      hI (fun _ => sq_nonneg _) (by rw [hb0]; norm_num)
  have hmass : Coulomb.mass oneElectronBumpState =
      (Fintype.card (Coulomb.Spins 1) : ℝ) * ∫ x : Configuration 1, oneElectronBump x ^ 2 := by
    simp only [Coulomb.mass, oneElectronBumpState, Coulomb.H1Vector.ofSmoothCompact,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [hmass]
  exact mul_pos (by norm_num [Coulomb.Spins]) hpos

def oneElectronTrial : Coulomb.H1Vector 1 :=
  oneElectronBumpState.rsmul (Real.sqrt (Coulomb.mass oneElectronBumpState))⁻¹

theorem oneElectronTrial_mass : Coulomb.mass oneElectronTrial = 1 := by
  rw [oneElectronTrial, Coulomb.mass_rsmul, inv_pow,
    Real.sq_sqrt oneElectronBumpState_mass_pos.le,
    inv_mul_cancel₀ oneElectronBumpState_mass_pos.ne']

end ContinuumCoulomb

end

end OAI
