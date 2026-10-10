import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorSplit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEnergyComponents

namespace OAI

/-! # Compact top-order commutator for a Schwartz coefficient

The concrete low-frequency part is compact by the kernel row argument.
The complementary high-frequency part is uniformly small by the proved
R⁻¹ estimate. No Rellich or compact-error hypothesis is assumed.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem commutator_split_energy (N : ℕ) (j : Fin N → Fin 12)
    (V f : 𝓢(E, ℂ)) (R : ℝ) (hR : 0 < R) :
    (∫ ξ : E, ‖radianFourierKernel (homogeneousOrderedCommutator N j V f) ξ‖ ^ 2) ≤
      2 * ((∫ ξ : E, ‖radianFourierKernel (homogeneousOrderedCommutator N j V
        (homogeneousLowFrequencyPart R hR f)) ξ‖ ^ 2) +
        ∫ ξ : E, ‖radianFourierKernel (homogeneousOrderedCommutator N j V
          (homogeneousHighFrequencyPart R hR f)) ξ‖ ^ 2) := by
  let F := radianFourierKernel (homogeneousOrderedCommutator N j V f)
  let L := radianFourierKernel (homogeneousOrderedCommutator N j V (homogeneousLowFrequencyPart R hR f))
  let H := radianFourierKernel (homogeneousOrderedCommutator N j V (homogeneousHighFrequencyPart R hR f))
  have he : F = L + H := by
    change radianFourierCLM (homogeneousOrderedCommutator N j V f) = _
    rw [homogeneousOrderedCommutator_split N j V f R hR, map_add]
    rfl
  have hF := (F.memLp 2).integrable_norm_pow (p := 2) (by norm_num)
  have hL := (L.memLp 2).integrable_norm_pow (p := 2) (by norm_num)
  have hH := (H.memLp 2).integrable_norm_pow (p := 2) (by norm_num)
  have hp (ξ : E) : ‖F ξ‖ ^ 2 ≤ 2 * (‖L ξ‖ ^ 2 + ‖H ξ‖ ^ 2) := by
    have hfξ : F ξ = L ξ + H ξ := by rw [he, add_apply]
    rw [hfξ]
    have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (L ξ) (H ξ)) 2
    nlinarith [sq_nonneg (‖L ξ‖ - ‖H ξ‖)]
  have hi := integral_mono hF ((hL.add hH).const_mul 2) hp
  rw [integral_const_mul] at hi
  simp only [Pi.add_apply] at hi
  rw [integral_add hL hH] at hi
  exact hi

theorem tendsto_homogeneousSchwartzCommutator_fourierL2 (a M : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (j : Fin (N + 1) → Fin 12) (V : 𝓢(E, ℂ)) (f : ℕ → 𝓢(E, ℂ))
    (hf : ∀ n, ‖homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk (f n)‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk (f n)))
        atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ξ : E,
      ‖radianFourierKernel (homogeneousOrderedCommutator (N + 1) j V (f n)) ξ‖ ^ 2)
      atTop (𝓝 0) := by
  let c : ℝ := ((2 * Real.pi) ^ (12 : ℕ))⁻¹
  let J : ℝ := ∫ ξ : E, homogeneousCommutatorMoment N V ξ
  let D := M ^ 2 / c
  have hc : 0 < c := by dsimp [c]; positivity
  have henergy (n : ℕ) : homogeneousFrequencyEnergy (N + 1) (radianFourierKernel (f n)) ≤ D := by
    have hn := pow_le_pow_left₀ (norm_nonneg _)
      ((homogeneousHighEnergy_norm_le a ((N + 1 : ℕ) : ℝ) ha1 hk
        (homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk (f n))).trans (hf n)) 2
    change ‖homogeneousHighEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk
      (homogeneousFrequencyEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk (radianFourierKernel (f n)))‖ ^ 2 ≤ M ^ 2 at hn
    rw [homogeneousHighEnergy_Schwartz_norm_sq] at hn
    exact (le_div_iff₀ hc).mpr (by simpa only [c, Nat.cast_add, Nat.cast_one, mul_comm] using hn)
  have htail : Tendsto (fun r : ℕ => ((c * J) / (r : ℝ)) ^ 2 * D) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using
      ((tendsto_const_div_atTop_nhds_zero_nat (c * J)).pow 2).mul_const D
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n => hb.trans_le (integral_nonneg (fun ξ => sq_nonneg _)))
  · intro ε hε
    have hsmall := htail.eventually (gt_mem_nhds (show 0 < ε / 4 by linarith))
    obtain ⟨r, hr1, hr⟩ := ((eventually_ge_atTop (1 : ℕ)).and hsmall).exists
    have hR : 1 ≤ (r : ℝ) := by exact_mod_cast hr1
    have hRp : 0 < (r : ℝ) := by linarith
    have hl := tendsto_homogeneousLowCommutator_fourier_L2 a ((N + 1 : ℕ) : ℝ) M r ha ha1 hk hR
      (N + 1) j V f hf hweak
    have hlow := hl.eventually (gt_mem_nhds (show 0 < ε / 4 by linarith))
    filter_upwards [hlow] with n hn
    have hh : (∫ ξ : E, ‖radianFourierKernel
        (homogeneousOrderedCommutator (N + 1) j V
          (homogeneousHighFrequencyPart r hRp (f n))) ξ‖ ^ 2) < ε / 4 := by
      have he := (homogeneousHighFrequencyPart_energy_le (N + 1) r (by positivity) hRp (f n)).trans
        (henergy n)
      calc
        _ ≤ (c / (r : ℝ) * J) ^ 2 *
            homogeneousFrequencyEnergy (N + 1)
              (radianFourierKernel (homogeneousHighFrequencyPart r hRp (f n))) :=
          homogeneousOrderedCommutator_high_energy N j V
            (homogeneousHighFrequencyPart r hRp (f n)) r hR
            (homogeneousHighFrequencyPart_zero r hRp (f n))
        _ ≤ (c / (r : ℝ) * J) ^ 2 * D := mul_le_mul_of_nonneg_left he (sq_nonneg _)
        _ = ((c * J) / (r : ℝ)) ^ 2 * D := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring
        _ < ε / 4 := hr
    have hb := commutator_split_energy (N + 1) j V (f n) r hRp
    linarith

theorem tendsto_homogeneousSchwartzCommutator_physicalL2 (a M : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (j : Fin (N + 1) → Fin 12) (V : 𝓢(E, ℂ)) (f : ℕ → 𝓢(E, ℂ))
    (hf : ∀ n, ‖homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk (f n)‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk (f n)))
        atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : E, ‖homogeneousOrderedCommutator (N + 1) j V (f n) x‖ ^ 2)
      atTop (𝓝 0) := by
  have ht := tendsto_homogeneousSchwartzCommutator_fourierL2 a M N ha ha1 hk j V f hf hweak
  have he (n : ℕ) : (∫ x : E, ‖homogeneousOrderedCommutator (N + 1) j V (f n) x‖ ^ 2) =
      ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        ∫ ξ : E, ‖radianFourierKernel (homogeneousOrderedCommutator (N + 1) j V (f n)) ξ‖ ^ 2 := by
    have h := radianFourier_energy_zero (homogeneousOrderedCommutator (N + 1) j V (f n))
    simp only [homogeneousFrequencyEnergy, mul_zero, Real.rpow_zero, one_mul] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  simp_rw [he]
  simpa only [mul_zero] using ht.const_mul (((2 * Real.pi) ^ (12 : ℕ))⁻¹)

end DefocusingNLS

end OAI
