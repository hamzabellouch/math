import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedLinearOrbitals
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedFourIndex
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombPacketTests
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteCoefficientCorrection

namespace OAI

/-! Coulomb integrals of actual linear combinations of the localized
orbitals. Bounded-L1 packets make the full four-index change of basis an
exact identity, with joint singular-kernel integrability. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb
namespace CoulombPacket

theorem sumList_apply (fs : List CoulombPacket) (x : Position) :
    sumList fs x = (fs.map (fun f => f x)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simpa only [sumList, add, List.map_cons, List.sum_cons] using congrArg (fun t => f x + t) ih

theorem combination_apply {m : ℕ} (f : Fin m → CoulombPacket) (a : Fin m → ℝ) (x : Position) :
    combination f a x = ∑ j, a j * f j x := by
  rw [combination, sumList_apply, List.map_ofFn, List.sum_ofFn]
  rfl

end CoulombPacket

def localizedLinearTransitionPacket {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b : Fin m → ℝ) : CoulombPacket :=
  CoulombPacket.combination
    (fun j => CoulombPacket.combination (fun k => localizedTransitionPacket hfreq (u j) (u k))
      (fun k => a j * b k)) (fun _ => 1)

theorem localizedLinearTransitionPacket_apply {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b : Fin m → ℝ) (x : Position) :
    localizedLinearTransitionPacket hfreq u a b x =
      localizedLinearOrbital freq u a x * localizedLinearOrbital freq u b x := by
  simp only [localizedLinearTransitionPacket, CoulombPacket.combination_apply, one_mul,
    localizedTransitionPacket, localizedTransition, localizedLinearOrbital, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

def localizedLinearFourIndex {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b c d : Fin m → ℝ) : ℝ :=
  CoulombPacket.pair (localizedLinearTransitionPacket hfreq u a b)
    (localizedLinearTransitionPacket hfreq u c d)

theorem localizedLinearFourIndex_integrable {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b c d : Fin m → ℝ) :
    Integrable (fun p : Position × Position =>
      (localizedLinearOrbital freq u a p.1 * localizedLinearOrbital freq u b p.1) *
      (localizedLinearOrbital freq u c p.2 * localizedLinearOrbital freq u d p.2) *
      Coulomb.coulombKernel (p.1 - p.2)) := by
  simpa only [localizedLinearTransitionPacket_apply] using
    CoulombPacket.joint_integrable (localizedLinearTransitionPacket hfreq u a b)
      (localizedLinearTransitionPacket hfreq u c d)

theorem localizedLinearFourIndex_integral {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b c d : Fin m → ℝ) :
    localizedLinearFourIndex hfreq u a b c d =
      ∫ p : Position × Position,
        (localizedLinearOrbital freq u a p.1 * localizedLinearOrbital freq u b p.1) *
        (localizedLinearOrbital freq u c p.2 * localizedLinearOrbital freq u d p.2) *
        Coulomb.coulombKernel (p.1 - p.2) := by
  simp only [localizedLinearFourIndex, CoulombPacket.pair, localizedLinearTransitionPacket_apply]

theorem localizedLinearFourIndex_eq {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b c d : Fin m → ℝ) :
    localizedLinearFourIndex hfreq u a b c d =
      ∑ j, ∑ k, ∑ l, ∑ r,
        ((a j * b k) * (c l * d r)) * localizedFourIndex freq (u j) (u k) (u l) (u r) := by
  unfold localizedLinearFourIndex localizedLinearTransitionPacket
  rw [CoulombPacket.pair_combination_left]
  simp_rw [CoulombPacket.pair_combination_left, CoulombPacket.pair_combination_right,
    localizedTransitionPacket_pair hfreq, Finset.mul_sum, one_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem localizedLinearFourIndex_correction {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (A : Fin m → Fin m → ℝ) {eta : ℝ}
    (he : 0 ≤ eta) (hA : ∀ i j, |A i j| ≤ 2)
    (hnear : ∀ i j, |A i j - if i = j then 1 else 0| ≤ eta) (i j k l : Fin m) :
    |localizedLinearFourIndex hfreq u (A i) (A j) (A k) (A l) -
      localizedFourIndex freq (u i) (u j) (u k) (u l)| ≤
      (m : ℝ)^4 * (32 * eta * localizedPotentialBound freq) := by
  have hF (p q r s : Fin m) :
      |localizedFourIndex freq (u p) (u q) (u r) (u s)| ≤ localizedPotentialBound freq := by
    rw [abs_of_nonneg (localizedFourIndex_nonnegative hfreq _ _ _ _)]
    have hov : planarModeOverlap (u p) (u q) ≤ 1 := by
      rw [← localizedTransition_mass hfreq]
      exact localizedTransition_mass_le_one hfreq _ _
    exact (localizedFourIndex_le_overlap hfreq _ _ _ _).trans
      ((mul_le_mul_of_nonneg_left hov (localizedPotentialBound_nonnegative freq)).trans_eq (mul_one _))
  rw [localizedLinearFourIndex_eq]
  exact finiteFourIndexChange_bound A (fun p q r s => localizedFourIndex freq (u p) (u q) (u r) (u s))
    he (localizedPotentialBound_nonnegative freq) hA hnear hF i j k l

end ContinuumCoulomb

end

end OAI
