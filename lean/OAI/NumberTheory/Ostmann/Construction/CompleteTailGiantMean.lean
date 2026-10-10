import OAI.NumberTheory.Ostmann.Construction.TailMaskCollision
import OAI.NumberTheory.Ostmann.Preliminaries.MertensShortBlockMass

namespace OAI

/-! # The original giant mean from favorable primes and tail collisions

All prime laws in the conclusion are the full smooth harmonic cell laws.
The favorable set is only a mask on the Fourier test, never on the prior.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tailGiantPhysical (A : Set ℕ) (N : ℕ) (F : Finset ℕ)
    (p : ℕ) [Fact p.Prime] : ZMod p → ℂ :=
  phaseGiantPhysical (if p ∈ F then normalizedResidueTransform (tailDensityMask A N p)
    else fun _ => 0)

noncomputable def tailGiantEndpointMean (A : Set ℕ) (N : ℕ) (F E : Finset ℕ)
    (p : ℕ) : ℝ :=
  if hp : p.Prime then
    let _ : Fact p.Prime := ⟨hp⟩
    (E.card : ℝ)⁻¹ * ∑ a ∈ E, (tailGiantPhysical A N F p (a : ZMod p)).re
  else 0

theorem tailGiantEndpointMean_eq (A : Set ℕ) (N : ℕ) (F E : Finset ℕ)
    (p : ℕ) [Fact p.Prime] :
    tailGiantEndpointMean A N F E p =
      (E.card : ℝ)⁻¹ * ∑ a ∈ E, (tailGiantPhysical A N F p (a : ZMod p)).re := by
  simp only [tailGiantEndpointMean, dite_eq_left (Fact.out : p.Prime)]

/-- A finite form of (7.2). The remaining numerical premise compares the
favorable harmonic mass with the explicit collision loss and total cell
mass; it does not assume any mean of the giant test. -/
theorem tail_giant_positive_cell {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hdisjoint : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (F E D : Finset ℕ) (hFP : F ⊆ P) (ν : ℕ → ℝ)
    (lo hi γ δ B₀ : ℝ) (hlo : 4 < lo)
    (hsub : ∀ n ∈ logBlockCenters lo hi, smoothGiantPrimeRange n ⊆ P)
    (hFlog : ∀ p ∈ F, lo ≤ Real.log p ∧ Real.log p ≤ hi)
    (hFbal : ∀ p ∈ F, ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3)
    (hFγ : ∀ p (hp : p ∈ F), let _ : Fact p.Prime := ⟨hP p (hFP hp)⟩;
      γ ≤ (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖)
    (hE : ∀ p ∈ P, ∀ a ∈ E, a ∈ A ∧ N + p < a)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p E D
      (fun _ => (E.card : ℝ)⁻¹) ν) ≤ B₀)
    (hgap :
      δ * (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p) +
        Real.sqrt (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p) *
          Real.sqrt (B₀ / (lo - 4)) < (γ / 2) * ∑ p ∈ F, (p : ℝ)⁻¹) :
    ∃ n ∈ logBlockCenters lo hi,
      0 < smoothGiantMass (smoothGiantPrimeRange n) logCellProfile n ∧
      δ < ∑ p : smoothGiantPrimeRange n,
        smoothGiantPrior (smoothGiantPrimeRange n) logCellProfile n p *
          tailGiantEndpointMean A N F E p := by
  let : ∀ p : P, Fact (p : ℕ).Prime := fun p => ⟨hP p p.property⟩
  let C := logBlockCenters lo hi
  let w : P → ℝ := fun p => (p : ℝ)⁻¹ * logCellFamilyWeight C p
  let Fs : Finset P := Finset.univ.filter fun p => (p : ℕ) ∈ F
  have hw (p : P) : 0 ≤ w p := mul_nonneg (by positivity) (logCellFamilyWeight_nonneg _ _)
  have hFs (p : P) : p ∈ Fs ↔ (p : ℕ) ∈ F := by simp [Fs]
  have hmass : (∑ p : P, w p) = ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p :=
    Finset.sum_coe_sort P (fun p : ℕ => (p : ℝ)⁻¹ * logCellFamilyWeight C p)
  have hFav : (∑ p ∈ Fs, w p) = ∑ p ∈ F, (p : ℝ)⁻¹ := by
    have he : P.filter (fun p => p ∈ F) = F := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hFP h, h⟩⟩
    calc
      (∑ p ∈ Fs, w p) = ∑ p ∈ P, if p ∈ F then (p : ℝ)⁻¹ * logCellFamilyWeight C p else 0 := by
        simp only [Fs, Finset.sum_filter]
        exact Finset.sum_coe_sort P (fun p : ℕ =>
          if p ∈ F then (p : ℝ)⁻¹ * logCellFamilyWeight C p else 0)
      _ = ∑ p ∈ F, (p : ℝ)⁻¹ * logCellFamilyWeight C p := by rw [← Finset.sum_filter, he]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [logBlockCenters_partition lo hi p (hFlog p hp).1 (hFlog p hp).2, mul_one]
  have hb := tailDensityMask_weighted_collision hA hB N P hP hdisjoint E D
    (fun _ => (E.card : ℝ)⁻¹) ν w (lo - 4) B₀ (by linarith)
    (logBlock_family_collision_weight P hP lo hi hlo) hbudget
  have he := favorablePhase_empirical_mean_lower (fun p : P => (p : ℕ))
    (fun p => tailDensityMask A N p) Fs
    (fun p => zmodResidueMass E (fun _ => (E.card : ℝ)⁻¹) p)
    w hw γ (B₀ / (lo - 4))
    (fun p _ => (Finset.image_nonempty.mpr (tailSupport_nonempty hA N p (hP p p.property).pos)))
    (fun p hp => by
      rw [tailDensityMask_card]
      have hh := hFbal p ((hFs p).mp hp)
      have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (hP p p.property).pos
      exact_mod_cast (show ((tailSupport A N p).card : ℝ) < p by linarith))
    (fun p hp => tailDensityMask_density A N p (hP p p.property).pos (hFbal p ((hFs p).mp hp)))
    (fun p hp => hFγ p ((hFs p).mp hp)) hb
  have hphysical (p : P) : favorablePhaseTransform (fun p : P => (p : ℕ))
      (fun p => tailDensityMask A N p) Fs p =
        (if (p : ℕ) ∈ F then normalizedResidueTransform (tailDensityMask A N p) else fun _ => 0) := by
    simp only [favorablePhaseTransform, hFs]
  have heq (p : P) :
      (∑ x ∈ tailDensityMask A N p, zmodResidueMass E (fun _ => (E.card : ℝ)⁻¹) p x *
        (phaseGiantPhysical (favorablePhaseTransform (fun p : P => (p : ℕ))
          (fun p => tailDensityMask A N p) Fs p) x).re) =
      tailGiantEndpointMean A N F E p := by
    rw [hphysical, tailDensityMask_empirical_mean A N p (hP p p.property).pos E
      (fun _ => (E.card : ℝ)⁻¹) _ (hE p p.property)]
    rw [tailGiantEndpointMean_eq, Finset.mul_sum]
    rfl
  simp_rw [heq] at he
  rw [hmass, hFav] at he
  have htotal : (∑ p : P, w p * tailGiantEndpointMean A N F E p) =
      ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p * tailGiantEndpointMean A N F E p :=
    Finset.sum_coe_sort P (fun p : ℕ =>
      (p : ℝ)⁻¹ * logCellFamilyWeight C p * tailGiantEndpointMean A N F E p)
  rw [htotal] at he
  apply complete_smoothGiantPrior_exists_positive_mean P hP C hsub
    (tailGiantEndpointMean A N F E) δ
  dsimp only [C] at he ⊢
  linarith

end Ostmann

end OAI
