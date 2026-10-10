import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedTransition

namespace OAI

/-! Four-index Coulomb integrals of the actual localized orbitals. Each
unequal-index pair gives exponentially small Coulomb coefficients, uniformly
in the other pair. Diagonal pairs recover the actual direct interaction. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedPotentialBound_nonnegative (freq : ℝ) : 0 ≤ localizedPotentialBound freq := by
  unfold localizedPotentialBound NeutralAtom.kernelBallMass
  exact add_nonneg (mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ =>
    NeutralAtom.coulombKernel_nonneg _))) zero_le_one

theorem localizedTransition_coulomb_integrable_bound {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) :
    Integrable (fun y => NeutralAtom.coulombKernel (x - y) * localizedTransition freq u v y) ∧
      NeutralAtom.potentialOf (localizedTransition freq u v) x ≤ localizedPotentialBound freq := by
  have h := NeutralAtom.bounded_density_convolution NeutralAtom.measurable_coulombKernel
    NeutralAtom.coulombKernel_nonneg (NeutralAtom.coulombKernel_integrableOn_ball 1)
    (fun _ => NeutralAtom.coulombKernel_le_one) (localizedTransition_integrable hfreq u v)
    (localizedTransition_nonnegative hfreq u v) (localizedTransition_bound hfreq u v) x
  refine ⟨h.1, h.2.trans ?_⟩
  exact add_le_add_right (localizedTransition_mass_le_one hfreq u v) _

theorem localizedTransition_potential_nonnegative {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedTransition freq u v) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedTransition_nonnegative hfreq u v _))

theorem localizedTransition_potential_continuous {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) : Continuous (NeutralAtom.potentialOf (localizedTransition freq u v)) :=
  NeutralAtom.potentialOf_continuous (localizedTransition_integrable hfreq u v)
    (localizedTransition_nonnegative hfreq u v) (localizedTransition_bound hfreq u v)

def localizedFourIndex (freq : ℝ) (u v w z : PlanarPosition) : ℝ :=
  ∫ x, localizedTransition freq u v x * NeutralAtom.potentialOf (localizedTransition freq w z) x

theorem localizedFourIndex_integrable {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    Integrable (fun x => localizedTransition freq u v x *
      NeutralAtom.potentialOf (localizedTransition freq w z) x) := by
  apply (localizedTransition_integrable hfreq u v).mul_bdd (c := localizedPotentialBound freq)
    (localizedTransition_potential_continuous hfreq w z).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (localizedTransition_potential_nonnegative hfreq w z x)]
    exact (localizedTransition_coulomb_integrable_bound hfreq w z x).2)

theorem localizedFourIndex_nonnegative {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    0 ≤ localizedFourIndex freq u v w z :=
  integral_nonneg (fun _ => mul_nonneg (localizedTransition_nonnegative hfreq u v _)
    (localizedTransition_potential_nonnegative hfreq w z _))

theorem localizedTransitionPacket_pair {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    CoulombPacket.pair (localizedTransitionPacket hfreq u v) (localizedTransitionPacket hfreq w z) =
      localizedFourIndex freq u v w z := by
  unfold CoulombPacket.pair localizedFourIndex NeutralAtom.potentialOf
  rw [Measure.volume_eq_prod, integral_prod _ (CoulombPacket.joint_integrable _ _)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  change localizedTransition freq u v x * localizedTransition freq w z y * ‖x - y‖⁻¹ =
    localizedTransition freq u v x * (‖x - y‖⁻¹ * localizedTransition freq w z y)
  ring

theorem localizedFourIndex_symmetric {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    localizedFourIndex freq u v w z = localizedFourIndex freq w z u v := by
  rw [← localizedTransitionPacket_pair hfreq, CoulombPacket.pair_symmetric,
    localizedTransitionPacket_pair hfreq]

theorem localizedFourIndex_diagonal (freq : ℝ) (u v : PlanarPosition) :
    localizedFourIndex freq u u v v = localizedCoulombCoeff freq u v := by
  have he (w : PlanarPosition) : localizedTransition freq w w = localizedDensity freq w := by
    funext x
    exact (pow_two _).symm
  simp only [localizedFourIndex, localizedCoulombCoeff, he]

theorem localizedFourIndex_le_overlap {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    localizedFourIndex freq u v w z ≤ localizedPotentialBound freq * planarModeOverlap u v := by
  have h := integral_mono (localizedFourIndex_integrable hfreq u v w z)
    ((localizedTransition_integrable hfreq u v).mul_const (localizedPotentialBound freq))
    (fun x => mul_le_mul_of_nonneg_left (localizedTransition_coulomb_integrable_bound hfreq w z x).2
      (localizedTransition_nonnegative hfreq u v x))
  rw [integral_mul_const, localizedTransition_mass hfreq] at h
  exact h.trans_eq (mul_comm _ _)

def localizedFourIndexConstant (freq : ℝ) : ℝ := localizedPotentialBound freq * planarOverlapConstant

theorem localizedFourIndexConstant_nonnegative (freq : ℝ) : 0 ≤ localizedFourIndexConstant freq :=
  mul_nonneg (localizedPotentialBound_nonnegative freq) planarOverlapConstant_nonnegative

theorem localizedFourIndex_decay_left {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    |localizedFourIndex freq u v w z| ≤
      localizedFourIndexConstant freq * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖) := by
  rw [abs_of_nonneg (localizedFourIndex_nonnegative hfreq u v w z)]
  calc
    _ ≤ localizedPotentialBound freq * planarModeOverlap u v := localizedFourIndex_le_overlap hfreq u v w z
    _ ≤ localizedPotentialBound freq * (planarOverlapConstant * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖)) :=
      mul_le_mul_of_nonneg_left (planarModeOverlap_decay u v) (localizedPotentialBound_nonnegative freq)
    _ = _ := (mul_assoc _ _ _).symm

theorem localizedFourIndex_decay_right {freq : ℝ} (hfreq : 0 < freq) (u v w z : PlanarPosition) :
    |localizedFourIndex freq u v w z| ≤
      localizedFourIndexConstant freq * Real.exp (-(9 / 10 : ℝ) * ‖w - z‖) := by
  rw [localizedFourIndex_symmetric hfreq]
  exact localizedFourIndex_decay_left hfreq w z u v

theorem localizedFourIndex_offsite {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (i j k l : Fin m) (hoff : i ≠ j ∨ k ≠ l) :
    |localizedFourIndex freq (u i) (u j) (u k) (u l)| ≤
      localizedFourIndexConstant freq * Real.exp (-(9 / 10 : ℝ) * D) := by
  rcases hoff with hij | hkl
  · exact (localizedFourIndex_decay_left hfreq _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsep i j hij]))
        (localizedFourIndexConstant_nonnegative freq))
  · exact (localizedFourIndex_decay_right hfreq _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsep k l hkl]))
        (localizedFourIndexConstant_nonnegative freq))

end ContinuumCoulomb

end

end OAI
