import OAI.MeasureTheory.Falconer.Slicing.GaussianFourier

namespace OAI

/-! Fixed-support Fourier moment bounds with a total derivative budget. -/

namespace Falconer
open Set MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.closedBall (0 : Space n) 1)).toReal

theorem integral_compact_derivative_bound {n : ℕ} (φ : 𝓢(Space n, ℂ))
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Space n) 1)
    (k : ℕ) {B : ℝ}
    (hd : ∀ x, ‖iteratedFDeriv ℝ k φ x‖ ≤ B) :
    (∫ x : Space n, ‖iteratedFDeriv ℝ k φ x‖) ≤ unitBallVolume n * B := by
  have hi : Integrable (fun x : Space n => ‖iteratedFDeriv ℝ k φ x‖) := by
    simpa using φ.integrable_pow_mul_iteratedFDeriv volume 0 k
  have he : (∫ x in Metric.closedBall (0 : Space n) 1, ‖iteratedFDeriv ℝ k φ x‖) =
      ∫ x : Space n, ‖iteratedFDeriv ℝ k φ x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx' : x ∉ Function.support (iteratedFDeriv ℝ k (φ : Space n → ℂ)) :=
      fun h => hx (hs ((support_iteratedFDeriv_subset k) h))
    simpa only [Function.mem_support, not_not, norm_eq_zero] using hx'
  rw [← he]
  calc
    _ ≤ ∫ _x in Metric.closedBall (0 : Space n) 1, B :=
      integral_mono hi.integrableOn (integrableOn_const measure_closedBall_lt_top.ne) hd
    _ = _ := by simp [unitBallVolume, measureReal_def]

theorem compact_fourier_decay {n m : ℕ} (φ : 𝓢(Space n, ℂ))
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Space n) 1)
    {B : ℝ} (_hB : 0 ≤ B)
    (hd : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k φ x‖ ≤ B) (ξ : Space n) :
    ‖ξ‖^m * ‖𝓕 φ ξ‖ ≤ (2 : ℝ)^m * (m+1) * unitBallVolume n * B := by
  have hh := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := ⊤) (φ.smooth ⊤)
    (fun k j _ _ => φ.integrable_pow_mul_iteratedFDeriv volume k j)
    (k := 0) (n := m) (by simp) (by simp) ξ
  have hsum : (∑ p ∈ Finset.range (0+1) ×ˢ Finset.range (m+1),
      ∫ x : Space n, ‖x‖^p.1 * ‖iteratedFDeriv ℝ p.2 φ x‖) ≤
      (m+1) * (unitBallVolume n * B) := by
    calc
      _ ≤ ∑ _p ∈ Finset.range (0+1) ×ˢ Finset.range (m+1), unitBallVolume n * B := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_product.mp hp
        have hp0 : p.1 = 0 := by simpa using hp'.1
        have hp2 : p.2 ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hp'.2)
        simpa [hp0] using integral_compact_derivative_bound φ hs p.2 (hd p.2 hp2)
      _ = _ := by simp
  calc
    _ ≤ (2 : ℝ)^m * _ := by simpa [SchwartzMap.fourier_coe] using hh
    _ ≤ (2 : ℝ)^m * ((m+1) * (unitBallVolume n * B)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem compact_inverse_fourier_decay {n m : ℕ} (φ : 𝓢(Space n, ℂ))
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Space n) 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hd : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k φ x‖ ≤ B) (ξ : Space n) :
    ‖ξ‖^m * ‖𝓕⁻ φ ξ‖ ≤ (2 : ℝ)^m * (m+1) * unitBallVolume n * B := by
  have h := compact_fourier_decay φ hs hB hd (-ξ)
  simpa [SchwartzMap.fourierInv_apply_eq] using h

theorem compact_inverse_fourier_moment_bound (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space n, ℂ)),
      tsupport φ ⊆ Metric.closedBall (0 : Space n) 1 →
      ∀ B : ℝ, 0 ≤ B →
      (∀ j ≤ k+n+1, ∀ x, ‖iteratedFDeriv ℝ j φ x‖ ≤ B) →
      (∫ ξ : Space n, ‖ξ‖^k * ‖𝓕⁻ φ ξ‖) ≤ C * B := by
  let q := n+1
  let A := (2 : ℝ)^(k+q) * ((k+q : ℕ)+1) * unitBallVolume n
  let W := ∫ x : Space n, (1+‖x‖)^(-(q : ℝ))
  refine ⟨2^q * W * (unitBallVolume n + A), by
    dsimp [W, A, unitBallVolume]
    positivity, ?_⟩
  intro φ hs B hB hd
  have h0 (ξ : Space n) : ‖𝓕⁻ φ ξ‖ ≤ unitBallVolume n * B := by
    have h := compact_inverse_fourier_decay (m := 0) φ hs hB
      (fun j hj => hd j (by omega)) ξ
    simpa using h
  have htop (ξ : Space n) : ‖ξ‖^(k+q) * ‖𝓕⁻ φ ξ‖ ≤ A * B := by
    exact compact_inverse_fourier_decay φ hs hB (fun j hj => hd j (by dsimp [q] at hj; omega)) ξ
  have hW : Integrable (fun x : Space n => (1+‖x‖)^(-(q : ℝ))) := by
    apply integrable_one_add_norm
    simp [Space, q]
  calc
    _ ≤ ∫ ξ : Space n, (2^q * (unitBallVolume n * B + A * B)) *
        (1+‖ξ‖)^(-(q : ℝ)) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ξ => by positivity) (hW.const_mul _)
      filter_upwards with ξ
      exact pow_mul_le_of_le_of_pow_mul_le (norm_nonneg ξ) (norm_nonneg _) (h0 ξ) (htop ξ)
    _ = _ := by rw [integral_const_mul]; dsimp [W]; ring

end Falconer

end OAI
