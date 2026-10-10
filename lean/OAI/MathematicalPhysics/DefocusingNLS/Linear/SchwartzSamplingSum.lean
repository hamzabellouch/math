import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzCutoffAnnulusSampling

namespace OAI

/-! # Finite sums of sampled physical annuli

Sampling respects the actual physical Fourier transform.  Consequently the
uniform annular estimate can be summed before passing to a full cutoff profile.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def schwartzTorusSamplingLinear (a k L : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) : 𝓢(E, ℂ) →ₗ[ℂ] FourierL2 where
  toFun := schwartzTorusSample a k L ha1 hk hL
  map_add' := by
    intro K J
    ext n
    change (expandingSobolevWeight a k L n : ℂ) *
        schwartzLatticeCoefficient L (K + J) n =
      (expandingSobolevWeight a k L n : ℂ) * schwartzLatticeCoefficient L K n +
        (expandingSobolevWeight a k L n : ℂ) * schwartzLatticeCoefficient L J n
    simp only [schwartzLatticeCoefficient, add_apply]
    ring
  map_smul' := by
    intro c K
    ext n
    change (expandingSobolevWeight a k L n : ℂ) *
        schwartzLatticeCoefficient L (c • K) n =
      c * ((expandingSobolevWeight a k L n : ℂ) * schwartzLatticeCoefficient L K n)
    simp only [schwartzLatticeCoefficient, smul_apply, smul_eq_mul]
    ring

noncomputable def physicalSchwartzTorusSamplingLinear (a k L : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) : 𝓢(E, ℂ) →ₗ[ℂ] FourierL2 :=
  (schwartzTorusSamplingLinear a k L ha1 hk hL).comp radianFourierCLM.toLinearMap

@[simp] theorem physicalSchwartzTorusSamplingLinear_apply (a k L : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (ψ : 𝓢(E, ℂ)) :
    physicalSchwartzTorusSamplingLinear a k L ha1 hk hL ψ =
      schwartzTorusSample a k L ha1 hk hL (radianFourierKernel ψ) := rfl

theorem schwartzTorusSample_physical_sum {ι : Type*} (S : Finset ι)
    (a k L : ℝ) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (ψ : ι → 𝓢(E, ℂ)) :
    schwartzTorusSample a k L ha1 hk hL (radianFourierKernel (∑ i ∈ S, ψ i)) =
      ∑ i ∈ S, schwartzTorusSample a k L ha1 hk hL (radianFourierKernel (ψ i)) := by
  exact map_sum (physicalSchwartzTorusSamplingLinear a k L ha1 hk hL) ψ S

theorem schwartzTorusSample_physical_sum_norm_le {ι : Type*} (S : Finset ι)
    (a k L : ℝ) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (ψ : ι → 𝓢(E, ℂ)) (B : ι → ℝ)
    (hB : ∀ i ∈ S, ‖schwartzTorusSample a k L ha1 hk hL
      (radianFourierKernel (ψ i))‖ ≤ B i) :
    ‖schwartzTorusSample a k L ha1 hk hL
      (radianFourierKernel (∑ i ∈ S, ψ i))‖ ≤ ∑ i ∈ S, B i := by
  rw [schwartzTorusSample_physical_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum hB)

theorem exists_cutoffProfileDyadicSum_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ κ : 𝓢(E, ℂ)) (hκ : HasCompactSupport (κ : E → ℂ))
    (hκann : ∀ x ∈ tsupport (κ : E → ℂ), (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
      (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∀ (L : ℝ) (hL : 1 ≤ L) (S : Finset ℕ), (∀ j ∈ S, (2 : ℝ) ^ j ≤ L) →
        ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
          (∑ j ∈ S, schwartzPhysicalDilation a ((2 : ℝ) ^ j) (by positivity)
            (cutoffProfileAnnulus a ((2 : ℝ) ^ j) L χ κ hκ Q hQ)))‖ ≤
          C * D / (1 - 2 ^ (-a)) := by
  obtain ⟨N, C, hC, hb⟩ := exists_cutoffProfileAnnulus_sampling_bound
    a k ha ha1 hk χ κ hκ hκann
  refine ⟨N, C, hC, ?_⟩
  intro Q hQ D hD hsymbol L hL S hSL
  have hr : ‖(2 ^ (-a) : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hB (j : ℕ) (hj : j ∈ S) :
      ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
        (schwartzPhysicalDilation a ((2 : ℝ) ^ j) (by positivity)
          (cutoffProfileAnnulus a ((2 : ℝ) ^ j) L χ κ hκ Q hQ)))‖ ≤
            (C * D) * (2 ^ (-a) : ℝ) ^ j := by
    have h := hb Q hQ D hD hsymbol ((2 : ℝ) ^ j) L
      (one_le_pow₀ (by norm_num)) (hSL j hj)
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] at h
    exact h
  calc
    _ ≤ ∑ j ∈ S, (C * D) * (2 ^ (-a) : ℝ) ^ j :=
      schwartzTorusSample_physical_sum_norm_le S a k L ha1 hk hL _ _ hB
    _ ≤ ∑' j : ℕ, (C * D) * (2 ^ (-a) : ℝ) ^ j :=
      ((summable_geometric_of_norm_lt_one hr).mul_left (C * D)).sum_le_tsum S
        (fun j _ => by positivity)
    _ = C * D / (1 - 2 ^ (-a)) := by
      rw [((hasSum_geometric_of_norm_lt_one hr).mul_left (C * D)).tsum_eq]
      rfl

end DefocusingNLS

end OAI
