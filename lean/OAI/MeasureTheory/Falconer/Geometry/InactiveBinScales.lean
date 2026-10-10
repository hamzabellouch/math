import OAI.MeasureTheory.Falconer.Fourier.UniformSymbolScale

namespace OAI

namespace PlanarFalconer

theorem dyadic_power_real (N : ℕ) (s : ℝ) :
    ((2 : ℝ)^N)^s = (2 : ℝ)^((N : ℝ)*s) := by
  rw [← Real.rpow_natCast (2 : ℝ) N, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

noncomputable def graphUncappedAngularScale (N : ℕ) (sig t : ℝ) : ℝ :=
  (2 : ℝ)^(-t) * ((2 : ℝ)^N)^(10*sig)

noncomputable def graphAngularScale (N : ℕ) (sig t c₀ : ℝ) : ℝ :=
  min c₀ (graphUncappedAngularScale N sig t)

theorem graphUncappedAngularScale_pos (N : ℕ) (sig t : ℝ) :
    0 < graphUncappedAngularScale N sig t := by
  unfold graphUncappedAngularScale
  positivity

theorem graphAngularScale_pos (N : ℕ) (sig t : ℝ) {c₀ : ℝ} (hc : 0 < c₀) :
    0 < graphAngularScale N sig t c₀ := lt_min hc (graphUncappedAngularScale_pos N sig t)

theorem graphAngularScale_cap_inactive {sig κ c₀ : ℝ}
    (hgap : 10*sig < κ) (hc : 0 < c₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t : ℝ, κ*(N : ℝ) ≤ t →
      graphAngularScale N sig t c₀ = graphUncappedAngularScale N sig t := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (sub_pos.mpr hgap) c₀⁻¹
  refine ⟨N₀,?_⟩
  intro N hN t ht
  apply min_eq_right
  have hb : graphUncappedAngularScale N sig t ≤ ((2 : ℝ)^N)^(sig*10-κ) := by
    simp only [graphUncappedAngularScale, dyadic_power_real, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hp : 0 < ((2 : ℝ)^N)^(κ-10*sig) := by positivity
  have hi := inv_anti₀ (inv_pos.mpr hc) (hN₀ N hN)
  simp only [inv_inv] at hi
  apply hb.trans
  convert hi using 1
  rw [show sig*10-κ = -(κ-10*sig) by ring, Real.rpow_neg (by positivity)]

theorem inactive_bin_scale_slack (N L : ℕ) {sig t u c Λ : ℝ}
    (hsig : 0 ≤ sig) (hc : 0 < c)
    (ht : t ≤ u+2*sig*(N : ℝ)) (hu : 10*sig*(N : ℝ) ≤ u)
    (hL : (L : ℝ) ≤ u+2*sig*(N : ℝ))
    (hΛ : c*(2 : ℝ)^(t+u) ≤ Λ) :
    c*((2 : ℝ)^N)^(18*sig) ≤ Λ*(graphUncappedAngularScale N sig t)^2 ∧
    sourceSymbolScale N sig L / (Λ*graphUncappedAngularScale N sig t) ≤
      c⁻¹*((2 : ℝ)^N)^(-19*sig) := by
  have hδ := graphUncappedAngularScale_pos N sig t
  have hΛp : 0 < Λ := (mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)).trans_le hΛ
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hδeq : (2 : ℝ)^(t+u)*graphUncappedAngularScale N sig t =
      (2 : ℝ)^u * ((2 : ℝ)^N)^(10*sig) := by
    unfold graphUncappedAngularScale
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 2
    ring
  constructor
  · have hb : ((2 : ℝ)^N)^(18*sig) ≤
        (2 : ℝ)^(t+u)*(graphUncappedAngularScale N sig t)^2 := by
      simp only [graphUncappedAngularScale, dyadic_power_real,
        ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      norm_num at *
      nlinarith
    exact (mul_le_mul_of_nonneg_left hb hc.le).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hΛ (sq_nonneg (graphUncappedAngularScale N sig t)))
  · have hD : sourceSymbolScale N sig L ≤ (2 : ℝ)^u * ((2 : ℝ)^N)^(-9*sig) := by
      unfold sourceSymbolScale
      rw [mul_max_of_nonneg _ _ (by positivity)]
      apply max_le
      · simp only [mul_one, dyadic_power_real, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith
      · rw [← Real.rpow_natCast (2 : ℝ) L]
        simp only [dyadic_power_real, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [mul_nonneg hsig hN]
    apply (div_le_iff₀ (mul_pos hΛp hδ)).mpr
    have he : (2 : ℝ)^u * ((2 : ℝ)^N)^(-9*sig) =
        (c⁻¹*((2 : ℝ)^N)^(-19*sig)) * (c*(2 : ℝ)^(t+u)*graphUncappedAngularScale N sig t) := by
      rw [mul_assoc c, hδeq]
      calc
        _ = (2 : ℝ)^u * (((2 : ℝ)^N)^(-19*sig) * ((2 : ℝ)^N)^(10*sig)) := by
          rw [← Real.rpow_add (by positivity)]
          congr 2
          ring
        _ = _ := by field_simp
    exact (hD.trans_eq he).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hΛ hδ.le) (by positivity))

end PlanarFalconer

end OAI
