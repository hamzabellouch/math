import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMultiples
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticResidueDecomposition

namespace OAI

/-! # The frequency summand and its exact quadratic normalization -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticFrequencyTerm {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (u : ℕ) : ℂ :=
  g (a * (u : ZMod q)) * realAdditivePhase (θ * u / q) * Φ ((u : ℝ) / (R * q))

theorem quadraticFrequencyTerm_at_square {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R : ℝ) (s v w : ℕ) :
    quadraticFrequencyTerm g a θ Φ R (s * v * w ^ 2) =
      quadraticDensityTerm g (a * (v : ZMod q)) θ Φ R v s w := by
  unfold quadraticFrequencyTerm quadraticDensityTerm
  rw [← realAdditivePhase_nat_mul]
  have hg : a * ((s * v * w ^ 2 : ℕ) : ZMod q) =
      a * (v : ZMod q) * (w : ZMod q) ^ 2 * (s : ZMod q) := by push_cast; ring
  have he : θ * ((s * v * w ^ 2 : ℕ) : ℝ) / q =
      (s : ℝ) * (θ * v * (w : ℝ) ^ 2 / q) := by push_cast; ring
  have hw : ((s * v * w ^ 2 : ℕ) : ℝ) / (R * q) =
      (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) := by push_cast; ring
  rw [hg, he, hw]

theorem quadraticFrequencyTerm_zero_above {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R H : ℝ) (N u : ℕ) (hR : 0 < R)
    (hN : H * R * q ≤ N) (hu : N < u)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    quadraticFrequencyTerm g a θ Φ R u = 0 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnu : (N : ℝ) < u := by exact_mod_cast hu
  have harg : H < (u : ℝ) / (R * q) := by
    apply (lt_div_iff₀ (mul_pos hR hqR)).mpr
    nlinarith
  simp only [quadraticFrequencyTerm, hΦ _ harg, mul_zero]

theorem quadratic_frequency_normalizer (q s v : ℕ) (R : ℝ)
    (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    (Real.sqrt (R * q) : ℂ)⁻¹ =
      (Real.sqrt (s : ℝ) : ℂ)⁻¹ * (Real.sqrt (v : ℝ) : ℂ)⁻¹ *
        (Real.sqrt (R * q / ((s : ℝ) * v)) : ℂ)⁻¹ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hsC : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hsR).ne'
  have hvC : (Real.sqrt (v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hvR).ne'
  have hRC : (Real.sqrt (R * q) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos hR hqR)).ne'
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul hsR.le]
  push_cast
  field_simp

theorem positiveQuadraticMultiples_eq_frequency_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R H : ℝ) (s v P N : ℕ) (hR : 0 < R) (_hH : 0 ≤ H)
    (hs : 0 < s) (hv : 0 < v) (hP : 0 < P) (hN : 1 ≤ N)
    (hcut : H * R * q ≤ N) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    positiveQuadraticMultiples g (a * (v : ZMod q)) θ Φ R v s P =
      (Real.sqrt (R * q / ((s : ℝ) * v)) : ℂ)⁻¹ *
        ∑ w ∈ (Finset.Icc 1 N).filter (fun w => P ∣ w),
          quadraticFrequencyTerm g a θ Φ R (s * v * w ^ 2) := by
  classical
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  rw [positiveQuadraticMultiples_eq_cutoff g (a * (v : ZMod q)) θ Φ R v H s P hP hR hvR hs hΦ]
  congr 1
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hvR' : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hupper : Real.sqrt (H * R * q / ((s : ℝ) * v)) ≤ N := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < (s : ℝ) * v)).mpr
    have hsv : (1 : ℝ) ≤ (s : ℝ) * v := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsv (sq_nonneg (N : ℝ))]
  have hsub : quadraticCompactCutoff q R v H s ⊆ Finset.Icc 1 N := by
    intro w hw
    obtain ⟨hw0, hwW⟩ := Finset.mem_Ioc.mp hw
    refine Finset.mem_Icc.mpr ⟨hw0, ?_⟩
    have hb := (Nat.cast_le.mpr hwW).trans (Nat.floor_le (Real.sqrt_nonneg _))
    exact_mod_cast hb.trans hupper
  calc
    _ = ∑ w ∈ (Finset.Icc 1 N).filter (fun w => P ∣ w),
        quadraticDensityTerm g (a * (v : ZMod q)) θ Φ R v s w := by
      apply Finset.sum_subset (Finset.filter_subset_filter (fun w => P ∣ w) hsub)
      intro w hw hn
      obtain ⟨hw, hpw⟩ := Finset.mem_filter.mp hw
      by_contra hne
      have hm := quadraticDensityTerm_mem_cutoff g (a * (v : ZMod q)) θ Φ R v H s s w
        hR hvR hs le_rfl (Finset.mem_Icc.mp hw).1 hΦ hne
      exact hn (Finset.mem_filter.mpr ⟨hm, hpw⟩)
    _ = _ := by simp_rw [quadraticFrequencyTerm_at_square]

end Ostmann

end OAI
