import OAI.NumberTheory.JointDickman.Amplification.AmplificationArithmeticFeatures
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeKernelMeanBound

namespace OAI

/-! # Total positive arithmetic mass for removing remainder restrictions -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_positive_mass_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ j : ℕ, [NeZero j] →
        ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
        ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j →
        ∀ U V : ℕ,
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          T*amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) ≤
            ε B+K*(T/j)*singularSeries j := by
  obtain ⟨P,c,hc,H,m,hm,K,hK,ε,hε,hcomp⟩ :=
    amplification_arithmetic_feature_comparison hSD hSW hM hMP hη 1 (by norm_num)
  refine ⟨K+1,by linarith,ε,hε,?_⟩
  filter_upwards [hcomp] with B hb
  intro j _ Q hQ hscale hcut T hT hlog hlag U V hU hV
  obtain ⟨he,hkernel⟩ := hb j Q hQ hscale hcut T hT hlog hlag U V hU hV
    (fun _ => 1) (fun _ => 1) (by simp) (by simp)
  let E := ∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*
    fullPrimeMass (auxiliaryPrimes B) y*amplificationPrimeKernel P m B j c H T x y
  have hE : |E| ≤ K := primeKernel_mean_abs_le B _ hkernel
  have hSp := (singularSeries_bounds hMP j).1
  have hscalar : 0 ≤ singularSeries j/(j : ℝ) := div_nonneg hSp (Nat.cast_nonneg _)
  have hmodel : T*((singularSeries j/(j : ℝ))*E) ≤ T*((singularSeries j/(j : ℝ))*K) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ((le_abs_self E).trans hE) hscalar)
      (lt_of_lt_of_le zero_lt_one hT).le
  have herr : T*(amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1)-
      (singularSeries j/(j : ℝ))*E) ≤ ε B+(T/j)*singularSeries j := by
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) (lt_of_lt_of_le zero_lt_one hT).le).trans
      (by simpa only [mul_one,one_mul] using he)
  have hid : T*((singularSeries j/(j : ℝ))*K) = K*(T/j)*singularSeries j := by ring
  rw [hid] at hmodel
  nlinarith

end JointDickman

end OAI
