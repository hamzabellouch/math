import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongSieveScale

namespace OAI

/-! The actual long-completion dyad obeys the cubic-sieve estimate.
This theorem retains the original outer coefficients and all e-dependent
coprimality restrictions instead of bounding them by an abstract family. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_tail_dyad_sieve
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A S : Finset Eisenstein) (N U B C F E : ℝ),
      1 ≤ N → 0 < U → 0 ≤ B → 1 ≤ E →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ e ∈ S, primary e ∧ E ≤ norm e ∧ norm e ≤ 2*E) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ e ∈ S, ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0‖^2 ≤
        K*(N*(B*U))^ε*(B*U)*E^(2*ε)*
          (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_tail_level_sieve hε
  refine ⟨1296*K,by positivity,?_⟩
  intro w A S N U B C F E hN hU hB hE hA hS hcut α ℓ
  have hEp : 0 < E := zero_lt_one.trans_le hE
  let M : ℝ := K*(N*(B*U))^ε*(B*U)*E^(-2+2*ε)*
    (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let f : Eisenstein → ℂ := fun e => ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
    metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0
  have hb (e : Eisenstein) (he : e ∈ S) : ‖f e‖^2 ≤ M := by
    apply (hbound w A N U B C F hN hU hB hA hcut α ℓ e (hS e he).1).trans
    have hs := metaplectic_long_sieve_scale hE (hS e he).2.1
      (zero_lt_one.trans_le hN).le hU.le hB hε.le hεsmall
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hK.le)
      (Finset.sum_nonneg (fun r (_ : r ∈ A) => sq_nonneg ‖α r‖))
    simpa only [M,mul_assoc] using hh
  have hcard : (S.card:ℝ) ≤ 36*E := by
    have hs : S ⊆ primaryElementBall (2*E) := by
      intro e he
      exact mem_primaryElementBall.mpr ⟨(hS e he).1,(hS e he).2.2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans
      ((primaryElementBall_card_le (by positivity)).trans_eq (by ring))
  have hCS : ‖∑ e ∈ S, f e‖^2 ≤ (S.card:ℝ)*(∑ e ∈ S, ‖f e‖^2) := by
    simpa using complex_bilinear_rows_sq S (fun _ => (1:ℂ)) f
  change ‖∑ e ∈ S, f e‖^2 ≤ _
  calc
    _ ≤ (S.card:ℝ)*(∑ e ∈ S, ‖f e‖^2) := hCS
    _ ≤ (S.card:ℝ)*(∑ _e ∈ S, M) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum hb) (Nat.cast_nonneg _)
    _ = (S.card:ℝ)^2*M := by simp; ring
    _ ≤ (36*E)^2*M := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hM
    _ = _ := by
      calc
        _ = K*(N*(B*U))^ε*(B*U)*((36*E)^2*E^(-2+2*ε))*
            (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) := by
          dsimp [M]
          ring
        _ = _ := by rw [metaplectic_long_dyad_scale hEp]; ring

end CubicFirstMoment

end

end OAI
