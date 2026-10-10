import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedDualMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombPacketCoercivity

namespace OAI

/-! Coercivity of the actual full Coulomb Gram matrix of the localized
resolvent--Gaussian modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

def localizedPacket {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) : CoulombPacket where
  value := localizedDensity freq u
  continuous := localizedDensity_continuous freq u
  integrable := localizedDensity_integrable hfreq u
  bound := localizedAmplitudeBound freq ^ 2
  bound_nonnegative := sq_nonneg _
  bound_spec x := by
    rw [Real.norm_of_nonneg (localizedDensity_nonnegative freq u x)]
    exact localizedDensity_bound hfreq u x

theorem localizedPacket_pair {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    CoulombPacket.pair (localizedPacket hfreq u) (localizedPacket hfreq v) =
      localizedCoulombCoeff freq u v := by
  unfold CoulombPacket.pair localizedCoulombCoeff NeutralAtom.potentialOf
  rw [Measure.volume_eq_prod, integral_prod _ (CoulombPacket.joint_integrable _ _)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  change localizedDensity freq u x * localizedDensity freq v y * ‖x - y‖⁻¹ =
    localizedDensity freq u x * (‖x - y‖⁻¹ * localizedDensity freq v y)
  ring

theorem testCharge_localizedTest (χ : Position → ℝ) (u : PlanarPosition) (x : Position) :
    Coulomb.testCharge (localizedTest χ u) x = Coulomb.testCharge χ (x - planarCenter u) := by
  unfold Coulomb.testCharge localizedTest
  simp only [sub_eq_add_neg, NeutralAtom.coordinateLaplacian_translate]

theorem localizedTest_energy (χ : Position → ℝ) (u : PlanarPosition) :
    (∫ x, Coulomb.testCharge (localizedTest χ u) x * localizedTest χ u x) =
      ∫ x, Coulomb.testCharge χ x * χ x := by
  simp_rw [testCharge_localizedTest]
  exact integral_sub_right_eq_self (fun x => Coulomb.testCharge χ x * χ x) (planarCenter u)

def localDualEnergyBound : ℝ := |∫ x : Position, Coulomb.testCharge localDualBump x * localDualBump x| + 1

theorem localDualEnergyBound_positive : 0 < localDualEnergyBound := by
  unfold localDualEnergyBound
  positivity

theorem localizedGram_coercive {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hmargin : 0 ≤ localDualMass freq - m * localLeakageBound freq D) (d : Fin m → ℝ) :
    ((localDualMass freq - m * localLeakageBound freq D) ^ 2 / localDualEnergyBound) *
      ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j := by
  have h := CoulombPacket.gram_coercive_of_dual_lower (fun i => localizedPacket hfreq (u i))
    (fun i => localizedTest localDualBump (u i))
    (fun i => localizedTest_smooth localDualBump_smooth (u i))
    (fun i => localizedTest_hasCompactSupport localDualBump.hasCompactSupport (u i))
    (fun i j hij => localDualTests_disjoint hD (u i) (u j) (hsep i j hij))
    localDualEnergyBound_positive hmargin ?_ ?_ d
  · simpa only [localizedPacket_pair] using h
  · intro i
    rw [localizedTest_energy]
    exact (le_abs_self _).trans (by unfold localDualEnergyBound; linarith)
  · intro e
    have he := localizedDualMatrix_lower hfreq (by linarith : (3 : ℝ) ≤ D) u hsep e
    convert he using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change e i * e j * localizedDualPair freq (u i) (u j) localDualBump = _
    ring

end ContinuumCoulomb

end

end OAI
