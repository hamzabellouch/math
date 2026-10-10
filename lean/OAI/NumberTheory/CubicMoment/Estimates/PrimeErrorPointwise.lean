import OAI.NumberTheory.CubicMoment.Estimates.StructuredMeanValue
import OAI.NumberTheory.CubicMoment.Estimates.QuantitativeNoncube
import OAI.NumberTheory.CubicMoment.Estimates.StructuredSupportBounds

namespace OAI

/-! A pointwise power saving for the actual repeated-prime error. This
allows low-height character estimates to pass from independent prime
products to their squarefree restriction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma twistedErrorPrimePolynomial_pointwise_sq (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (χ : Eisenstein → ℂ) (hχ : ∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1)
    (ℓ : ℤ) (u t : ℝ) :
    ‖twistedErrorPrimePolynomial S w χ ℓ u t‖^2 ≤
      ((orderedConvolutionSupport S).card:ℝ)*
        ∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2 := by
  have he : (∑ b ∈ orderedConvolutionSupport S,
      ‖(squarefreeConvolutionError S w b*χ b)*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) ≤
      ∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2 := by
    apply Finset.sum_le_sum
    intro b hb
    apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
    rw [norm_mul,norm_mul,norm_mul,mellinPhase_norm,
      norm_theta (orderedConvolutionSupport_ne_zero S hS b hb),mul_one,mul_one]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (hχ b hb)
  exact (norm_sum_sq_le_card_mul (orderedConvolutionSupport S)
    (fun b => (squarefreeConvolutionError S w b*χ b)*theta ℓ b*mellinPhase (t+u) (norm b))).trans
      (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _))

theorem primeConvolutionError_cutoff_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y D : ℝ),
      0 ≤ Y → 0 < D → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1) →
      ∀ (ℓ : ℤ) (u t : ℝ),
      ‖twistedErrorPrimePolynomial S w χ ℓ u t‖ ≤
        K*Y*D^(-(1/4:ℝ))*((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  obtain ⟨C,hC,henergy⟩ := primeConvolutionError_energy_bound (ι := ι)
  refine ⟨Real.sqrt (18*C),Real.sqrt_pos.2 (by positivity),?_⟩
  intro S w M Y D hY hD hM hS hprod hw χ hχ ℓ u t
  have hprime : ∀ i, ∀ p ∈ S i, primaryPrime p := fun i p hp => (hS i p hp).1
  have hcard : ((orderedConvolutionSupport S).card:ℝ) ≤ 18*Y :=
    primary_support_card_le _ hY (fun z hz => by
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨orderedPrimarySupport_primary S (fun i p hp => (hprime i p hp).1)
        (Finset.mem_image.mpr ⟨f,hf,rfl⟩),hprod f hf⟩)
  let A : ℝ := ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i)
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  have hs := twistedErrorPrimePolynomial_pointwise_sq S w hprime χ hχ ℓ u t
  have hb := henergy S w M Y D hY hD hM hS hprod hw
  have htotal : ‖twistedErrorPrimePolynomial S w χ ℓ u t‖^2 ≤
      18*C*Y^2*D^(-(1/2:ℝ))*A^2 := by
    apply hs.trans
    calc
      _ ≤ (18*Y)*(C*Y*D^(-(1/2:ℝ))*A^2) :=
        mul_le_mul hcard hb (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
      _ = _ := by ring
  have heq : (Real.sqrt (18*C)*Y*D^(-(1/4:ℝ))*A)^2 =
      18*C*Y^2*D^(-(1/2:ℝ))*A^2 := by
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity),
      ← Real.rpow_natCast (D^(-(1/4:ℝ))) 2,← Real.rpow_mul hD.le]
    norm_num
  have hfinal := (sq_le_sq₀ (_root_.norm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hY)
      (Real.rpow_nonneg hD.le _)) hA)).mp (htotal.trans_eq heq.symm)
  simpa only [A,mul_assoc] using hfinal

theorem primeConvolutionError_pointwise_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y c : ℝ),
      0 < Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y^c < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1) →
      ∀ (ℓ : ℤ) (u t : ℝ),
      ‖twistedErrorPrimePolynomial S w χ ℓ u t‖ ≤
        K*Y^(1-c/4)*((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  obtain ⟨C,hC,henergy⟩ := primeConvolutionError_power_energy (ι := ι)
  refine ⟨Real.sqrt (18*C),Real.sqrt_pos.2 (by positivity),?_⟩
  intro S w M Y c hY hM hS hprod hw χ hχ ℓ u t
  have hprime : ∀ i, ∀ p ∈ S i, primaryPrime p := fun i p hp => (hS i p hp).1
  have hcard : ((orderedConvolutionSupport S).card:ℝ) ≤ 18*Y :=
    primary_support_card_le _ hY.le (fun z hz => by
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨orderedPrimarySupport_primary S (fun i p hp => (hprime i p hp).1)
        (Finset.mem_image.mpr ⟨f,hf,rfl⟩),hprod f hf⟩)
  let A : ℝ := ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i)
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  have hs := twistedErrorPrimePolynomial_pointwise_sq S w hprime χ hχ ℓ u t
  have hb := henergy S w M Y c hY hM hS hprod hw
  have htotal : ‖twistedErrorPrimePolynomial S w χ ℓ u t‖^2 ≤
      18*C*Y^(2-c/2)*A^2 := by
    apply hs.trans
    calc
      _ ≤ (18*Y)*(C*Y^(1-c/2)*A^2) :=
        mul_le_mul hcard hb (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
      _ = _ := by
        have he : Y*Y^(1-c/2) = Y^(2-c/2) := by
          calc
            _ = Y^(1:ℝ)*Y^(1-c/2) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hY]; congr 1; ring
        calc
          _ = 18*C*(Y*Y^(1-c/2))*A^2 := by ring
          _ = _ := by rw [he]
  have heq : (Real.sqrt (18*C)*Y^(1-c/4)*A)^2 = 18*C*Y^(2-c/2)*A^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),← Real.rpow_natCast (Y^(1-c/4)) 2,
      ← Real.rpow_mul hY.le]
    norm_num only [Nat.cast_ofNat]
    congr 2
    congr 1
    ring
  have hfinal := (sq_le_sq₀ (_root_.norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hY.le _)) hA)).mp
      (htotal.trans_eq heq.symm)
  simpa only [A,mul_assoc] using hfinal

end CubicFirstMoment

end

end OAI
