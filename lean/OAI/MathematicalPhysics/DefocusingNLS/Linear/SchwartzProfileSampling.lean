import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzDyadicCutoff
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzOuterAnnulusSampling

namespace OAI

/-! # Uniform expanding-torus bound for the entire cutoff profile

Only finitely many symbol derivatives are required.  The proof includes the
compact core, all inner dyadic annuli, and the final outer annulus.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem outer_annulus_decay (a L R : ℝ) (ha : 0 < a)
    (hL : 0 < L) (hR : 0 < R) (hR2 : R ≤ 2 * L) :
    L ^ (-a) ≤ 2 ^ a * R ^ (-a) := by
  have hp : (R / L) ^ a ≤ (2 : ℝ) ^ a :=
    Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hL).mpr hR2) ha.le
  have he : (R / L) ^ a * R ^ (-a) = L ^ (-a) := by
    rw [Real.div_rpow hR.le hL.le, Real.rpow_neg hR.le, Real.rpow_neg hL.le]
    field_simp
  calc
    _ = (R / L) ^ a * R ^ (-a) := he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hR.le _)

theorem exists_cutoffProfile_sampling_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0) :
    ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L),
        ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
          (cutoffProfileSchwartz L (by linarith) χ hχ Q hQ))‖ ≤ C := by
  obtain ⟨N₁, C₁, hC₁, hb₁⟩ := exists_cutoffProfileAnnulus_sampling_bound a k ha ha1 hk
    χ homogeneousAnnulusCutoff homogeneousAnnulusCutoff_hasCompactSupport
    homogeneousAnnulusCutoff_support
  obtain ⟨N₂, C₂, hC₂, hb₂⟩ := exists_outerCutoffAnnulus_sampling_bound a k ha ha1 hk
    χ homogeneousAnnulusCutoff homogeneousAnnulusCutoff_hasCompactSupport
    homogeneousAnnulusCutoff_support
  refine ⟨max N₁ N₂, ?_⟩
  intro Q hQ D hD hsymbol
  obtain ⟨C₀, hC₀, hcore⟩ := exists_schwartzCore_sampling_bound a k ha1 hk χ
    (profileCoreSchwartz Q hQ) (profileCoreSchwartz_hasCompactSupport Q hQ)
  let B := max C₁ (2 ^ a * C₂)
  have hB : 0 ≤ B := hC₁.trans (le_max_left _ _)
  have hr : ‖(2 ^ (-a) : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - (2 ^ (-a) : ℝ) := by
    have := lt_of_le_of_lt (le_abs_self (2 ^ (-a) : ℝ))
      (show |(2 ^ (-a) : ℝ)| < 1 by simpa only [Real.norm_eq_abs] using hr)
    linarith
  refine ⟨C₀ + B * D / (1 - 2 ^ (-a)), add_nonneg hC₀ (by positivity), ?_⟩
  intro L hL
  have hLp : 0 < L := by linarith
  let P := physicalSchwartzTorusSamplingLinear a k L ha1 hk hL
  let ψ : ℕ → 𝓢(E, ℂ) := fun j =>
    schwartzPhysicalDilation a ((2 : ℝ) ^ j) (by positivity)
      (cutoffProfileAnnulus a ((2 : ℝ) ^ j) L χ homogeneousAnnulusCutoff
        homogeneousAnnulusCutoff_hasCompactSupport Q hQ)
  have hψ (j : ℕ) : ‖P (ψ j)‖ ≤ (B * D) * (2 ^ (-a) : ℝ) ^ j := by
    have hRp : 0 < (2 : ℝ) ^ j := by positivity
    have hR : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have he : ((2 : ℝ) ^ j) ^ (-a) = (2 ^ (-a) : ℝ) ^ j :=
      (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    by_cases hRL : (2 : ℝ) ^ j ≤ L
    · have h := hb₁ Q hQ D hD
        (fun n hn => hsymbol n (hn.trans (le_max_left _ _))) ((2 : ℝ) ^ j) L hR hRL
      change ‖P (ψ j)‖ ≤ C₁ * D * ((2 : ℝ) ^ j) ^ (-a) at h
      exact h.trans (by rw [he]; gcongr; exact le_max_left _ _)
    · by_cases hR2 : (2 : ℝ) ^ j ≤ 2 * L
      · have h := hb₂ Q hQ D hD
          (fun n hn => hsymbol n (hn.trans (le_max_right _ _))) L ((2 : ℝ) ^ j) hL
            (le_of_lt (lt_of_not_ge hRL)) hR2
        change ‖P (ψ j)‖ ≤ C₂ * D * L ^ (-a) at h
        calc
          _ ≤ C₂ * D * L ^ (-a) := h
          _ ≤ C₂ * D * (2 ^ a * ((2 : ℝ) ^ j) ^ (-a)) :=
            mul_le_mul_of_nonneg_left (outer_annulus_decay a L ((2 : ℝ) ^ j) ha hLp hRp hR2)
              (mul_nonneg hC₂ hD)
          _ = (2 ^ a * C₂) * D * ((2 : ℝ) ^ j) ^ (-a) := by ring
          _ ≤ B * D * ((2 : ℝ) ^ j) ^ (-a) := by gcongr; exact le_max_right _ _
          _ = _ := by rw [he]
      · have hz : ψ j = 0 := cutoffProfileAnnulus_zero_of_large_radius a ((2 : ℝ) ^ j) L
          hLp (le_of_lt (lt_of_not_ge hR2)) χ hχzero Q hQ
        rw [hz, map_zero, norm_zero]
        positivity
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (2 * L) (by norm_num : (1 : ℝ) < 2)
  have hs : ‖P (∑ j ∈ Finset.range J, ψ j)‖ ≤ B * D / (1 - 2 ^ (-a)) := by
    rw [map_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range J, ‖P (ψ j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range J, (B * D) * (2 ^ (-a) : ℝ) ^ j :=
        Finset.sum_le_sum (fun j _ => hψ j)
      _ ≤ ∑' j : ℕ, (B * D) * (2 ^ (-a) : ℝ) ^ j :=
        ((summable_geometric_of_norm_lt_one hr).mul_left (B * D)).sum_le_tsum _
          (fun j _ => by positivity)
      _ = _ := by rw [((hasSum_geometric_of_norm_lt_one hr).mul_left (B * D)).tsum_eq]; rfl
  rw [cutoffProfileSchwartz_dyadic_assembly a L hLp χ hχ hχzero Q hQ J hJ.le]
  change ‖P (_ + ∑ j ∈ Finset.range J, ψ j)‖ ≤ _
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add (hcore L hL) hs)

end DefocusingNLS

end OAI
