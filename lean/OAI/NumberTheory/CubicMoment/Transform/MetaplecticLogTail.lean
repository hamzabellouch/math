import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTailDyad
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily

namespace OAI

/-! The long-tail cubic estimate for the original logarithmically
varying weights, obtained by exact scalar normalization. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplecticAngularSmoothSum_const_mul (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (U t : ℝ) (z : ℂ) :
    metaplecticAngularSmoothSum r ℓ (fun x => z*W x) U t =
      z*metaplecticAngularSmoothSum r ℓ W U t := by
  unfold metaplecticAngularSmoothSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  ring

lemma logarithmic_tail_energy {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {s X : ℝ} (hs : 0 < s) (hX : 1 ≤ X)
    (w : Eisenstein → γ) (A : Finset Eisenstein) (hY : ∀ r ∈ A, Y (w r) ≤ X) (α : Eisenstein → ℂ) :
    (∑ r ∈ A, ‖α r*(((Y (w r))^s:ℝ):ℂ)‖^2) ≤ X^(2*s)*(∑ r ∈ A, ‖α r‖^2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hy : 0 < Y (w r) := zero_lt_one.trans_le (hW.length_one (w r))
  have hp : ((Y (w r))^s)^2 ≤ X^(2*s) := by
    calc
      _ ≤ (X^s)^2 := pow_le_pow_left₀ (Real.rpow_nonneg hy.le _)
        (Real.rpow_le_rpow hy.le (hY r hr) hs.le) 2
      _ = _ := by
        rw [←Real.rpow_mul_natCast (zero_lt_one.trans_le hX).le]
        congr 1
        push_cast
        ring
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hy.le _),mul_pow]
  exact (mul_le_mul_of_nonneg_left hp (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem LogarithmicWeightFamily.metaplectic_tail_dyad_sieve
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {ε s : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A S : Finset Eisenstein) (X N U B C F E : ℝ),
      1 ≤ X → 1 ≤ N → 0 < U → 0 ≤ B → 1 ≤ E →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ e ∈ S, primary e ∧ E ≤ norm e ∧ norm e ≤ 2*E) →
      (∀ r ∈ A, Y (w r) ≤ X) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ e ∈ S, ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0‖^2 ≤
        K*X^(2*s)*(N*(B*U))^ε*(B*U)*E^(2*ε)*
          (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := (hW.normalize hs).metaplectic_tail_dyad_sieve hε hεsmall
  refine ⟨K,hK,?_⟩
  intro w A S X N U B C F E hX hN hU hB hE hA hS hY hcut α ℓ
  let α' : Eisenstein → ℂ := fun r => α r*(((Y (w r))^s:ℝ):ℂ)
  have hncut (r : Eisenstein) (hr : r ∈ A) (x : ℝ) (hx : B < x) :
      normalizedLogWeight Y W s (w r) x = 0 := by
    simp only [normalizedLogWeight,hcut r hr x hx,smul_zero]
  have hb := hbound w A S N U B C F E hN hU hB hE hA hS hncut α' ℓ
  have heq : (∑ e ∈ S, ∑ r ∈ A, α' r*metaplecticTailCoefficient r ℓ C F e*
      metaplecticAngularSmoothSum r ℓ (normalizedLogWeight Y W s (w r)) (U/norm e^3) 0) =
      ∑ e ∈ S, ∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0 := by
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro r _
    have hy : 0 < Y (w r) := zero_lt_one.trans_le (hW.length_one (w r))
    have hlin : metaplecticAngularSmoothSum r ℓ (normalizedLogWeight Y W s (w r)) (U/norm e^3) 0 =
        (((Y (w r))^(-s):ℝ):ℂ)*metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0 := by
      change metaplecticAngularSmoothSum r ℓ (fun x => ((Y (w r))^(-s):ℝ) • W (w r) x) _ _ = _
      simp_rw [Complex.real_smul]
      exact metaplecticAngularSmoothSum_const_mul r ℓ (W (w r)) _ _ _
    have hp : (((Y (w r))^s:ℝ):ℂ)*(((Y (w r))^(-s):ℝ):ℂ) = 1 := by
      rw [←Complex.ofReal_mul,←Real.rpow_add hy,add_neg_cancel,Real.rpow_zero,Complex.ofReal_one]
    rw [hlin]
    dsimp [α']
    calc
      _ = ((((Y (w r))^s:ℝ):ℂ)*(((Y (w r))^(-s):ℝ):ℂ))*
          (α r*metaplecticTailCoefficient r ℓ C F e*
            metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0) := by ring
      _ = _ := by rw [hp,one_mul]
  rw [heq] at hb
  apply hb.trans
  have henergy := logarithmic_tail_energy hW hs hX w A hY α
  calc
    _ ≤ K*(N*(B*U))^ε*(B*U)*E^(2*ε)*
        (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ))*(X^(2*s)*(∑ r ∈ A, ‖α r‖^2)) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
