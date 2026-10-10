import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOddCommutator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPolynomialMoment

namespace OAI

/-! # Radius-uniform high-frequency gain for the complete odd-power linearization -/

open scoped SchwartzMap

namespace DefocusingNLS

attribute [local irreducible] expandingCircularCoefficient expandingAnticircularCoefficient
  expandingProduct expandingFourierCoefficient expandingOrderedFourierEnergy

noncomputable def oddCommutatorMomentBound (m : ℕ) (M : ℝ) : ℝ :=
  (m + 1 : ℕ) * (M ^ m * M ^ m) + (m : ℝ) * (M ^ (m + 1) * M ^ (m - 1))

theorem oddCommutatorMomentBound_nonneg (m : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ oddCommutatorMomentBound m M := by unfold oddCommutatorMomentBound; positivity

theorem oddCommutatorMomentBound_mono (m : ℕ) {M D : ℝ} (hM : 0 ≤ M) (hMD : M ≤ D) :
    oddCommutatorMomentBound m M ≤ oddCommutatorMomentBound m D := by
  unfold oddCommutatorMomentBound
  have hD : 0 ≤ D := hM.trans hMD
  gcongr

theorem expandingOddFourierCommutator_high_norm (a L R : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ))
    (hL : 1 ≤ L) (hR : 1 ≤ R) (m : ℕ) (q f : FourierL2) (j : Fin (N + 1) → Fin 12)
    (hq : Summable (latticeMomentMass L (N + 1) (expandingFourierCoefficient a (N + 1 : ℕ) L q)))
    (hf : ∀ n : frequencyLattice, ‖n‖ < R * L → f n = 0) :
    let M := ∑' n, latticeMomentMass L (N + 1) (expandingFourierCoefficient a (N + 1 : ℕ) L q) n
    ‖expandingOddFourierCommutator a L (N + 1) ha ha1 hN hL m q f j‖ ≤
      ((N + 1 : ℕ) / R) * 2 ^ N * oddCommutatorMomentBound m M * ‖f‖ := by
  intro M
  let A := expandingCircularCoefficient a (N + 1 : ℕ) L ha ha1 hN hL m q
  let B := expandingAnticircularCoefficient a (N + 1 : ℕ) L ha ha1 hN hL m q
  have hA := expandingCircular_moment a (N + 1 : ℕ) L ha ha1 hN hL (N + 1) m q hq
  have hB := expandingAnticircular_moment a (N + 1 : ℕ) L ha ha1 hN hL (N + 1) m q hq
  have hfconj : ∀ n : frequencyLattice, ‖n‖ < R * L → fourierConjugate f n = 0 := by
    intro n hn
    rw [fourierConjugate_apply, hf (-n) (by simpa only [norm_neg] using hn)]
    simp
  have hcA := expandingProductCommutator_high_moment a L R N ha ha1 hN hL hR j A f hA.1 hf
  have hcB := expandingProductCommutator_high_moment a L R N ha ha1 hN hL hR j B (fourierConjugate f) hB.1 hfconj
  rw [fourierConjugate_norm] at hcB
  rw [expandingOddFourierCommutator_eq, norm_smul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ ≤ ‖expandingProductCommutator a L (N + 1) ha ha1 hN hL j A f‖ +
        ‖expandingProductCommutator a L (N + 1) ha ha1 hN hL j B (fourierConjugate f)‖ := norm_add_le _ _
    _ ≤ ((N + 1 : ℕ) / R) * (2 ^ N * (∑' n, latticeMomentMass L (N + 1) (expandingFourierCoefficient a (N + 1 : ℕ) L A) n)) * ‖f‖ +
        ((N + 1 : ℕ) / R) * (2 ^ N * (∑' n, latticeMomentMass L (N + 1) (expandingFourierCoefficient a (N + 1 : ℕ) L B) n)) * ‖f‖ := add_le_add hcA hcB
    _ ≤ ((N + 1 : ℕ) / R) * (2 ^ N * ((m + 1 : ℕ) * (M ^ m * M ^ m))) * ‖f‖ +
        ((N + 1 : ℕ) / R) * (2 ^ N * ((m : ℝ) * (M ^ (m + 1) * M ^ (m - 1)))) * ‖f‖ := by
      gcongr
      · exact hA.2
      · exact hB.2
    _ = _ := by unfold oddCommutatorMomentBound; ring

theorem exists_expandingOddFourierCommutator_high_bound (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (K : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L R : ℝ) (hL : 1 ≤ L), 1 ≤ R →
      ∀ (f : FourierL2) (j : Fin (N + 1) → Fin 12),
        (∀ n : frequencyLattice, ‖n‖ < R * L → f n = 0) →
      ‖expandingOddFourierCommutator a L (N + 1) ha ha1 hN hL m
        (schwartzTorusSample a (N + 1 : ℕ) L ha1 hN hL K) f j‖ ≤ (C / R) * ‖f‖ := by
  obtain ⟨D, hD, hd⟩ := exists_schwartzPolynomialMoment_bound a (N + 1 : ℕ) ha ha1 hN (N + 1) K
  refine ⟨(N + 1 : ℕ) * 2 ^ N * oddCommutatorMomentBound m D, by
    exact mul_nonneg (by positivity) (oddCommutatorMomentBound_nonneg m D hD), ?_⟩
  intro L R hL hR f j hf
  let q := schwartzTorusSample a (N + 1 : ℕ) L ha1 hN hL K
  obtain ⟨hs, hb⟩ := hd L hL
  have hcoeff : expandingFourierCoefficient a (N + 1 : ℕ) L q = schwartzLatticeCoefficient L K := by
    funext n
    exact schwartzTorusSample_coefficient a (N + 1 : ℕ) L ha1 hN hL K n
  have hc := expandingOddFourierCommutator_high_norm a L R N ha ha1 hN hL hR m q f j
    (by simpa only [hcoeff] using hs) hf
  rw [hcoeff] at hc
  have hmass : 0 ≤ ∑' n, latticeMomentMass L (N + 1) (schwartzLatticeCoefficient L K) n :=
    tsum_nonneg (fun n => mul_nonneg
      (le_trans zero_le_one (latticeMomentWeight_one_le L hL (N + 1) n)) (norm_nonneg _))
  calc
    _ ≤ ((N + 1 : ℕ) / R) * 2 ^ N *
        oddCommutatorMomentBound m (∑' n, latticeMomentMass L (N + 1) (schwartzLatticeCoefficient L K) n) * ‖f‖ := hc
    _ ≤ ((N + 1 : ℕ) / R) * 2 ^ N * oddCommutatorMomentBound m D * ‖f‖ := by
      gcongr
      exact oddCommutatorMomentBound_mono m hmass hb
    _ = _ := by ring

end DefocusingNLS

end OAI
