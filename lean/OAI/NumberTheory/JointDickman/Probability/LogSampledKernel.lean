import OAI.NumberTheory.JointDickman.Probability.SampledMajorKernel
import OAI.NumberTheory.JointDickman.Amplification.LogOscillatoryTest

namespace OAI

/-! # The sampled major-arc kernel in its actual logarithmic coordinates -/

namespace JointDickman
open Finset
open scoped SchwartzMap

noncomputable def sampledEndpointKernel (m B j Q : ℕ) [NeZero j]
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ)
    (N β : ℝ) (w : 𝓢(ℝ,ℝ)) : ℂ :=
  sampledMajorKernel m B j Q J J g h
    (fun i => (w₁ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N) : ℂ))
    (fun i => (w₂ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N) : ℂ))
    (fun i => β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N))
    (fun i => β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N)) w

theorem logOscillatoryTest_sample_phase (w : ℝ → ℝ) (B N β ξ x : ℝ) :
    logOscillatoryTest w B N (β*ξ) x =
      (w (Real.exp (B*x)/N) : ℂ)*additivePhase (ξ*(β*(Real.exp (B*x)/N))) := by
  unfold logOscillatoryTest oscillatoryTest
  congr 2
  ring

theorem sampledEndpointKernel_eq (m B j Q : ℕ) [NeZero j]
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ)
    (N β : ℝ) (w : 𝓢(ℝ,ℝ)) :
    sampledEndpointKernel m B j Q J g h w₁ w₂ N β w =
      ∑ q ∈ positiveDenominators Q, ((ArithmeticFunction.moebius (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))*
        (∑ r : ZMod (j*(q : ℕ)), if r.val.Coprime (q : ℕ) then
          ∫ ξ : ℝ, testFourierTransform w ξ*
            (sampledProjectedFourier m B (j*(q : ℕ)) J g
              (fun i => logOscillatoryTest w₁ B N (β*ξ) (channelLower (channelFineCount m B) i)) r*
            sampledProjectedFourier m B (j*(q : ℕ)) J h
              (fun i => logOscillatoryTest w₂ B N (-β*ξ) (channelLower (channelFineCount m B) i)) (-r)) else 0) := by
  have hp (ξ : ℝ) :
      (fun i : Fin (channelFineCount m B) =>
        (w₁ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N) : ℂ)*
          additivePhase (ξ*(β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N)))) =
      fun i => logOscillatoryTest w₁ B N (β*ξ) (channelLower (channelFineCount m B) i) := by
    funext i
    exact (logOscillatoryTest_sample_phase w₁ B N β ξ _).symm
  have hn (ξ : ℝ) :
      (fun i : Fin (channelFineCount m B) =>
        (w₂ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N) : ℂ)*
          additivePhase (-ξ*(β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N)))) =
      fun i => logOscillatoryTest w₂ B N (-β*ξ) (channelLower (channelFineCount m B) i) := by
    funext i
    unfold logOscillatoryTest oscillatoryTest
    congr 2
    ring
  unfold sampledEndpointKernel sampledMajorKernel
  simp only [hp,hn,mul_assoc]

end JointDickman

end OAI
