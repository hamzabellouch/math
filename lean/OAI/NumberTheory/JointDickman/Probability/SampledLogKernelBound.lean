import OAI.NumberTheory.JointDickman.Probability.HistogramFourierRegularity
import OAI.NumberTheory.JointDickman.Probability.LogSampledKernel
import OAI.NumberTheory.JointDickman.Probability.GeometricHistogramErrors

namespace OAI

/-! # Summable size of the sampled logarithmic kernels -/

namespace JointDickman
open Finset MeasureTheory Filter
open scoped SchwartzMap Topology

theorem sampledProjectedValue_one_norm_le {m B : ℕ}
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : Fin (channelFineCount m B) → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ‖F i‖ ≤ M) :
    ‖sampledProjectedValue m B 1 J g F‖ ≤ Real.sqrt (manuscriptAmplitudeEnergy m B 1 J*M^2) := by
  have h := sampledProjectedFourier_norm_le (q := 1) hm hB J g hg F hM hF 0
  simpa only [sampledProjectedFourier_eq,ramanujanSum_zero,Nat.totient_one,
    Nat.cast_one,div_one,one_mul] using h

theorem sampledLogKernel_norm_le {m B : ℕ}
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (a b : Fin (channelFineCount m B) → ℂ)
    (x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (ha : ∀ i ∈ J, ‖a i‖ ≤ M₁) (hb : ∀ i ∈ J, ‖b i‖ ≤ M₂) :
    ‖sampledLogKernel m B J J g h a b x y w‖ ≤
      manuscriptAmplitudeEnergy m B 1 J*M₁*M₂*(∫ ξ : ℝ, ‖testFourierTransform w ξ‖) := by
  have hcut : 1 ≤ auxiliaryCutoff B := Nat.succ_le_of_lt (pow_pos hB _)
  have he := (sampledProjectedValue_fourier_inversion m B 1 J J g h a b x y w).trans
    (sampledLogKernel_residue_weights hm hB hcut J J g h a b x y w)
  rw [← he]
  let A := manuscriptAmplitudeEnergy m B 1 J
  have hA : 0 ≤ A := manuscriptAmplitudeEnergy_nonneg hm hB J
  have hsqrt : Real.sqrt (A*M₁^2)*Real.sqrt (A*M₂^2) = A*M₁*M₂ := by
    rw [Real.sqrt_mul hA,Real.sqrt_mul hA,Real.sqrt_sq_eq_abs,Real.sqrt_sq_eq_abs,
      abs_of_nonneg hM₁,abs_of_nonneg hM₂]
    calc
      _ = (Real.sqrt A)^2*(M₁*M₂) := by ring
      _ = _ := by rw [Real.sq_sqrt hA]; ring
  have hp (ξ : ℝ) :
      ‖sampledProjectedValue m B 1 J g (fun i => a i*additivePhase (ξ*x i))‖*
      ‖sampledProjectedValue m B 1 J h (fun i => b i*additivePhase (-ξ*y i))‖ ≤ A*M₁*M₂ := by
    rw [← hsqrt]
    apply mul_le_mul
    · apply sampledProjectedValue_one_norm_le hm hB J g hg _ hM₁
      intro i hi
      simpa only [norm_mul,norm_additivePhase,mul_one] using ha i hi
    · apply sampledProjectedValue_one_norm_le hm hB J h hh _ hM₂
      intro i hi
      simpa only [norm_mul,norm_additivePhase,mul_one] using hb i hi
    · exact norm_nonneg _
    · positivity
  calc
    _ ≤ ∫ ξ : ℝ, (A*M₁*M₂)*‖testFourierTransform w ξ‖ := by
      apply norm_integral_le_of_norm_le ((schwartz_testFourier_integrable w).norm.const_mul _)
      filter_upwards [] with ξ
      simp only [norm_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hp ξ) (norm_nonneg (testFourierTransform w ξ))]
    _ = _ := integral_const_mul _ _

theorem geometric_sampled_log_kernel_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {t L U : ℝ} (ht : 0 < t) (hLU : L ≤ U)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ S : Finset ℤ, ∀ β : ℝ, ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      (∑ k ∈ S, ‖sampledLogKernel m B
        (geometricHistogramWindow m B t L U k) (geometricHistogramWindow m B t L U k) g h
        (fun i => (w₁ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)) : ℂ))
        (fun i => (w₂ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)) : ℂ))
        (fun i => β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)))
        (fun i => β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t))) w‖) ≤ C/B := by
  obtain ⟨C,hC,he⟩ := manuscript_geometric_box_energy hSD hSW hM hMP
  let V := M₁*M₂*(∫ ξ : ℝ, ‖testFourierTransform w ξ‖)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hwidth : 0 ≤ U-L+2 := by linarith
  have hwidth' : 0 ≤ 1+U-L := by linarith
  have hover : 0 ≤ (1+U-L)/t+1 := by positivity
  refine ⟨(U-L+2)*C*((1+U-L)/t+1)*V,by positivity,?_⟩
  intro m hm
  filter_upwards [he m hm,eventually_ge_atTop 1] with B heB hB
  intro S β g h hg hh
  have hBpos : 0 < B := by omega
  have henergy := heB 1 (by omega) t L U ht hLU S
  simp only [Nat.cast_one,Nat.totient_one,div_self (one_ne_zero : (1 : ℝ) ≠ 0),one_mul] at henergy
  calc
    _ ≤ ∑ k ∈ S, manuscriptAmplitudeEnergy m B 1 (geometricHistogramWindow m B t L U k)*V := by
      apply sum_le_sum
      intro k _
      exact (sampledLogKernel_norm_le hm hBpos _ g h hg hh _ _ _ _ w hM₁ hM₂
        (fun _ _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hw₁ _)
        (fun _ _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hw₂ _)).trans_eq (by dsimp [V]; ring)
    _ = (∑ k ∈ S, manuscriptAmplitudeEnergy m B 1 (geometricHistogramWindow m B t L U k))*V :=
      (sum_mul _ _ _).symm
    _ ≤ (((U-L+2)/B)*C*((1+U-L)/t+1))*V := mul_le_mul_of_nonneg_right henergy hV
    _ = _ := by ring

end JointDickman

end OAI
