import OAI.Analysis.FiniteFactor.Polynomial
import OAI.Analysis.FiniteFactor.Convolution
import Mathlib.Data.Int.Interval

namespace OAI

namespace FiniteFactor
open scoped ComplexConjugate

/-- Sum a row of the Laurent coefficient double sum using its unique possible
second exponent. -/
theorem laurent_row_eq (K : ℕ) (A B : ℤ → ℂ) (r v : ℤ) :
    (∑ j : Fin (2*K+1), if v + ((j.val : ℤ)-K) = r then
      A v * B ((j.val : ℤ)-K) else 0) =
    if -(K : ℤ) ≤ r-v ∧ r-v ≤ K then A v * B (r-v) else 0 := by
  classical
  by_cases hv : -(K : ℤ) ≤ r-v ∧ r-v ≤ K
  · rw [ite_eq_left hv]
    let j : Fin (2*K+1) := ⟨(r-v+K).toNat, by omega⟩
    have hj : (j.val : ℤ)-K = r-v := by dsimp [j]; omega
    rw [Finset.sum_eq_single j]
    · rw [hj, ite_eq_left (by omega)]
    · intro b _ hb
      apply ite_eq_right
      intro he
      apply hb
      apply Fin.ext
      have := b.isLt
      omega
    · simp
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro j _
    apply ite_eq_right
    intro he
    apply hv
    have := j.isLt
    omega

/-- A finite subset of ℤ, exactly the two simultaneous coefficient cutoffs. -/
noncomputable def convolutionWindow (K : ℕ) (n : ℤ) : Finset ℤ :=
  (Finset.Icc (-(K : ℤ)) K).filter (fun v => -(K : ℤ) ≤ -n-v ∧ -n-v ≤ K)

theorem mem_convolutionWindow (K : ℕ) (n v : ℤ) :
    v ∈ convolutionWindow K n ↔ |v| ≤ (K : ℤ) ∧ |n+v| ≤ (K : ℤ) := by
  simp only [convolutionWindow, Finset.mem_filter, Finset.mem_Icc, abs_le]
  omega

theorem not_mem_convolutionWindow (K : ℕ) (n v : ℤ) :
    v ∉ convolutionWindow K n ↔ (K : ℤ) < |v| ∨ (K : ℤ) < |n+v| := by
  rw [mem_convolutionWindow]
  omega

theorem laurent_coefficient_eq_finite_convolution (K : ℕ) (A B : ℤ → ℂ) (n : ℤ) :
    laurentProductCoefficient K A B (-n) =
      ∑ v ∈ convolutionWindow K n, A v * B (-n-v) := by
  classical
  simp only [laurentProductCoefficient, laurent_row_eq]
  rw [convolutionWindow, Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => (i.val : ℤ)-K)
  · intro i _
    simp only [Finset.mem_Icc]
    have := i.isLt
    omega
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro v hv
    simp only [Finset.mem_Icc] at hv
    refine ⟨⟨(v+K).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp
    omega
  · intro i _
    rfl

/-- A zero absolutely convergent convolution forces the exact finite Laurent
coefficient to be the negative complementary tail. -/
theorem laurent_coefficient_eq_neg_tail (K : ℕ) (A B : ℤ → ℂ) (n : ℤ)
    (hs : Summable (fun v => A v * B (-n-v)))
    (hz : ∑' v, A v * B (-n-v) = 0) :
    laurentProductCoefficient K A B (-n) =
      -(∑' v : {v : ℤ // v ∉ convolutionWindow K n}, A v * B (-n-v)) := by
  rw [laurent_coefficient_eq_finite_convolution]
  exact finite_part_eq_neg_tail hs hz _

/-- The corresponding absolute tail bound used in error-pointwise. -/
theorem laurent_coefficient_norm_le_tail (K : ℕ) (A B : ℤ → ℂ) (n : ℤ)
    (hs : Summable (fun v => ‖A v * B (-n-v)‖))
    (hz : ∑' v, A v * B (-n-v) = 0) :
    ‖laurentProductCoefficient K A B (-n)‖ ≤
      ∑' v : {v : ℤ // v ∉ convolutionWindow K n}, ‖A v * B (-n-v)‖ := by
  rw [laurent_coefficient_eq_finite_convolution]
  exact finite_part_norm_le_tail hs hz _

/-- The full pointwise error estimate. The two exceptional masks remain
separate and each is summed over all of ℤ; no union bound is introduced. -/
theorem laurent_error_pointwise (K : ℕ) (n : ℤ)
    (ξ γ : lp (fun _ : ℤ => ℂ) 2) {F G : ℤ → ℝ}
    (hF : ∀ k, 0 < F k) (hG : ∀ k, 0 < G k)
    (hFa : Antitone F) (hGa : Antitone G) (hGF : ∀ k, G k ≤ F k)
    (hn : 0 ≤ n) {H₁ H₂ : Set ℤ} {ε : ℝ} (hε : 0 ≤ ε)
    (hz : ∑' v, leftCoefficient F ξ v * rightCoefficient G γ (-n-v) = 0)
    (hR : ∀ v, v ∉ convolutionWindow K n →
      G (n+v) / F v ≤ ε + H₁.indicator (fun _ => 1) v +
        H₂.indicator (fun _ => 1) v) :
    ‖laurentProductCoefficient K (leftCoefficient F ξ) (rightCoefficient G γ) (-n)‖ ≤
      ε * (‖ξ‖ * ‖γ‖) +
      (∑' v, H₁.indicator (fun v => ‖ξ v‖ * ‖γ (n+v)‖) v) +
      (∑' v, H₂.indicator (fun v => ‖ξ v‖ * ‖γ (n+v)‖) v) := by
  classical
  let p : ℤ → ℝ := fun v => ‖ξ v‖ * ‖γ (n+v)‖
  have hp0 : ∀ v, 0 ≤ p v := fun v => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨hp, hpbound⟩ := shifted_l2_norm_product ξ γ n
  change Summable p at hp
  change (∑' v, p v) ≤ ‖ξ‖ * ‖γ‖ at hpbound
  have hmask : ∀ H : Set ℤ, Summable (H.indicator p) := by
    intro H
    apply hp.of_nonneg_of_le
    · intro v
      by_cases hv : v ∈ H <;> simp [hv, hp0]
    · intro v
      by_cases hv : v ∈ H <;> simp [hv, hp0]
  let b : ℤ → ℝ := fun v => ε * p v + H₁.indicator p v + H₂.indicator p v
  have hb : Summable b := ((hp.mul_left ε).add (hmask H₁)).add (hmask H₂)
  have hb0 : ∀ v, 0 ≤ b v := by
    intro v
    dsimp [b]
    have h₁ : 0 ≤ H₁.indicator p v := by by_cases hv : v ∈ H₁ <;> simp [hv, hp0]
    have h₂ : 0 ≤ H₂.indicator p v := by by_cases hv : v ∈ H₂ <;> simp [hv, hp0]
    exact add_nonneg (add_nonneg (mul_nonneg hε (hp0 v)) h₁) h₂
  have hterm : ∀ v, v ∉ convolutionWindow K n →
      ‖leftCoefficient F ξ v * rightCoefficient G γ (-n-v)‖ ≤ b v := by
    intro v hv
    rw [cocycle_convolution_term_eq]
    have hr : 0 ≤ G (n+v) / F v := (div_pos (hG _) (hF _)).le
    simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr]
    calc
      G (n+v) / F v * ‖ξ v‖ * ‖γ (n+v)‖ = (G (n+v) / F v) * p v := by dsimp [p]; ring
      _ ≤ (ε + H₁.indicator (fun _ => 1) v + H₂.indicator (fun _ => 1) v) * p v :=
        mul_le_mul_of_nonneg_right (hR v hv) (hp0 v)
      _ = b v := by
        dsimp [b]
        by_cases h₁ : v ∈ H₁ <;> by_cases h₂ : v ∈ H₂ <;> simp [h₁, h₂] <;> ring
  have hs := (cocycle_convolution_absolute_convergence ξ γ hF hG hFa hGa hGF hn).1
  calc
    ‖laurentProductCoefficient K (leftCoefficient F ξ) (rightCoefficient G γ) (-n)‖ ≤
        ∑' v : {v : ℤ // v ∉ convolutionWindow K n},
          ‖leftCoefficient F ξ v * rightCoefficient G γ (-n-v)‖ :=
      laurent_coefficient_norm_le_tail K _ _ n hs hz
    _ ≤ ∑' v : {v : ℤ // v ∉ convolutionWindow K n}, b v :=
      (hs.subtype _).tsum_le_tsum (fun v => hterm v v.property) (hb.subtype _)
    _ ≤ ∑' v, b v := hb.tsum_subtype_le _ _ hb0
    _ = ε * (∑' v, p v) + (∑' v, H₁.indicator p v) + (∑' v, H₂.indicator p v) := by
      change (∑' v, (ε * p v + H₁.indicator p v + H₂.indicator p v)) = _
      rw [Summable.tsum_add ((hp.mul_left ε).add (hmask H₁)) (hmask H₂),
        Summable.tsum_add (hp.mul_left ε) (hmask H₁), tsum_mul_left]
    _ ≤ _ := by
      change ε * (∑' v, p v) + (∑' v, H₁.indicator p v) + (∑' v, H₂.indicator p v) ≤
        ε * (‖ξ‖ * ‖γ‖) + (∑' v, H₁.indicator p v) + (∑' v, H₂.indicator p v)
      linarith [mul_le_mul_of_nonneg_left hpbound hε]

end FiniteFactor

end OAI
