import OAI.NumberTheory.JointDickman.Probability.GeometricCoarseKernel

namespace OAI

/-! # Identifying the sampled arc expression with the real spatial kernel -/

namespace JointDickman
open Finset
open scoped SchwartzMap

noncomputable def sampledEndpointLogKernel (m B : ℕ)
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ)
    (N β : ℝ) (w : 𝓢(ℝ,ℝ)) : ℂ :=
  sampledLogKernel m B J J g h
    (fun i => (w₁ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N) : ℂ))
    (fun i => (w₂ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N) : ℂ))
    (fun i => β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N))
    (fun i => β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N)) w

theorem geometric_sampled_kernel_identity (m B : ℕ) (t L U β : ℝ)
    (S : Finset ℤ) (d : ℤ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) :
    (B : ℂ)*(∑ k ∈ S, (d k : ℂ)*sampledEndpointLogKernel m B
      (geometricHistogramWindow m B t L U k) g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w) =
    (cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h)
      (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β d w₁ w₂ w)) : ℂ) := by
  rw [geometricWindowKernel_bilinear]
  push_cast
  congr 1
  apply sum_congr rfl
  intro k _
  unfold sampledEndpointLogKernel
  rw [sampledLogKernel_real]
  push_cast
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  unfold endpointSpatialWeight
  push_cast
  ring

theorem sampledEndpointKernel_singularSeries_error
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {m B j Q : ℕ} [NeZero j] (hm : 0 < m) (hB : 0 < B)
    (hcut : j*Q ≤ auxiliaryCutoff B)
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ)
    (N β : ℝ) (w : 𝓢(ℝ,ℝ)) :
    ‖sampledEndpointKernel m B j Q J g h w₁ w₂ N β w-
      (singularSeries j : ℂ)*sampledEndpointLogKernel m B J g h w₁ w₂ N β w‖ ≤
      ((j : ℝ)/j.totient)*singularSeriesTail (Q+1)*
        ‖sampledEndpointLogKernel m B J g h w₁ w₂ N β w‖ :=
  sampledMajorKernel_singularSeries_error hMP hm hB hcut J J g h _ _ _ _ w

end JointDickman

end OAI
