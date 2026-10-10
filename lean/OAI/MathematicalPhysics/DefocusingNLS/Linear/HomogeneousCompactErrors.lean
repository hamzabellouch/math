import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCompactLocalEstimate
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedCommutator

namespace OAI

/-! # The whole-space compact-error estimate for the actual potential

The fractional low-order term and the entire ordered top-derivative error
are bounded by an arbitrarily small Y term and a fixed-ball physical L²
observation. Fourier estimates and density establish the compactness
needed for the potential and commutator terms.
-/

open MeasureTheory Filter Topology

namespace DefocusingNLS

theorem homogeneousLinearizedTopCommutator_local_estimate (a ε : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (j : Fin (N + 1) → Fin 12) (m : ℕ) (q : HomogeneousY a ((N + 1 : ℕ) : ℝ))
    (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : HomogeneousY a ((N + 1 : ℕ) : ℝ),
      ‖homogeneousLinearizedTopCommutator a N ha ha1 hk j m q u‖ ≤ ε * ‖u‖ +
        C * ‖homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) R ha ha1 hk u‖ := by
  exact homogeneousCompactOperator_local_estimate a ((N + 1 : ℕ) : ℝ) ha ha1 hk
    (homogeneousLinearizedTopCommutator a N ha ha1 hk j m q)
    (fun M u hu hw => tendsto_homogeneousLinearizedTopCommutator a M N ha ha1 hk j m q u hu hw)
    ε hε

theorem homogeneousLinearizedLowEnergy_local_estimate (a k ε : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : HomogeneousY a k,
      ‖homogeneousLowEnergy a k ha1 hk (homogeneousLinearizedPotential a k ha ha1 hk (m + 1) q u)‖ ≤
        ε * ‖u‖ + C * ‖homogeneousLocalL2Observation a k R ha ha1 hk u‖ := by
  let T := ((homogeneousLowEnergy a k ha1 hk).restrictScalars ℝ).comp
    (homogeneousLinearizedPotential a k ha ha1 hk (m + 1) q)
  exact homogeneousCompactOperator_local_estimate a k ha ha1 hk T
    (fun M u hu hw => tendsto_homogeneousLowEnergy_linearizedPotential a k M ha ha1 hk m q u hu hw)
    ε hε

theorem homogeneousLinearized_compact_errors (a ε : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (q : HomogeneousY a ((N + 1 : ℕ) : ℝ)) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : HomogeneousY a ((N + 1 : ℕ) : ℝ),
      ‖homogeneousLowEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk
        (homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u)‖ +
      Real.sqrt (∑ j : Fin (N + 1) → Fin 12,
        ‖homogeneousLinearizedTopCommutator a N ha ha1 hk j m q u‖ ^ 2) ≤
      ε * ‖u‖ + C * ‖homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) R ha ha1 hk u‖ := by
  let J := Fin (N + 1) → Fin 12
  let d : ℝ := Fintype.card J
  have hd : 0 < d := by
    change (0 : ℝ) < (Fintype.card J : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  let δ := ε / (2 * d)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hd)
  obtain ⟨R₀, hR₀, C₀, hC₀, h₀⟩ := homogeneousLinearizedLowEnergy_local_estimate a
    ((N + 1 : ℕ) : ℝ) (ε / 2) ha ha1 hk m q (half_pos hε)
  have htop (j : J) := homogeneousLinearizedTopCommutator_local_estimate a δ N ha ha1 hk j m q hδ
  choose R hR C hC hc using htop
  let Rall := R₀ + ∑ j : J, R j
  let Call := C₀ + ∑ j : J, C j
  have hRsum : 0 ≤ ∑ j : J, R j := Finset.sum_nonneg (fun j _ => (hR j).le)
  have hCall : 0 ≤ Call := add_nonneg hC₀ (Finset.sum_nonneg (fun j _ => hC j))
  refine ⟨Rall, by dsimp [Rall]; linarith, Call, hCall, fun u => ?_⟩
  let O := ‖homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) Rall ha ha1 hk u‖
  have hlow := h₀ u
  have hO₀ : ‖homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) R₀ ha ha1 hk u‖ ≤ O :=
    homogeneousLocalL2Observation_norm_mono a ((N + 1 : ℕ) : ℝ) R₀ Rall ha ha1 hk
      (by dsimp [Rall]; linarith) u
  have hOj (j : J) : ‖homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) (R j) ha ha1 hk u‖ ≤ O := by
    have hj := Finset.single_le_sum (fun j _ => (hR j).le) (Finset.mem_univ j)
    apply homogeneousLocalL2Observation_norm_mono a ((N + 1 : ℕ) : ℝ) (R j) Rall ha ha1 hk
    dsimp [Rall]
    linarith
  have hs : (∑ j : J, ‖homogeneousLinearizedTopCommutator a N ha ha1 hk j m q u‖) ≤
      (ε / 2) * ‖u‖ + (∑ j : J, C j) * O := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun (j : J) _ =>
      (hc j u).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hOj j) (hC j))))
    have he : (Fintype.card J : ℝ) * δ = ε / 2 := by
      change d * δ = ε / 2
      dsimp [δ]
      field_simp [hd.ne']
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.sum_mul, ← mul_assoc, he] using h
  have hroot : Real.sqrt (∑ j : J, ‖homogeneousLinearizedTopCommutator a N ha ha1 hk j m q u‖ ^ 2) ≤
      ∑ j : J, ‖homogeneousLinearizedTopCommutator a N ha ha1 hk j m q u‖ := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨Finset.sum_nonneg (fun _ _ => norm_nonneg _),
      Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)⟩
  have hlow' := hlow.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hO₀ hC₀))
  dsimp only [Call]
  nlinarith

end DefocusingNLS

end OAI
