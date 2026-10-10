import OAI.NumberTheory.JointDickman.Probability.SampledKernelInversion
import OAI.NumberTheory.JointDickman.Probability.ResidueAverageMass
import OAI.NumberTheory.JointDickman.Amplification.SingularSeriesTruncation

namespace OAI

/-! # The retained sampled kernel and its singular-series limit -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

noncomputable def sampledLogKernel (m B : ℕ)
    (J K : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (a b : Fin (channelFineCount m B) → ℂ)
    (x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ)) : ℂ :=
  ∑ i ∈ J, ∑ k ∈ K, ((logCellSignedMass m B g i : ℂ)*a i)*
    ((logCellSignedMass m B h k : ℂ)*b k)*(w (x i-y k) : ℂ)

noncomputable def sampledMajorKernel (m B j Q : ℕ) [NeZero j]
    (J K : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (a b : Fin (channelFineCount m B) → ℂ)
    (x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ)) : ℂ :=
  ∑ q ∈ positiveDenominators Q, ((μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))*
    (∑ r : ZMod (j*(q : ℕ)), if r.val.Coprime (q : ℕ) then
      ∫ ξ : ℝ, testFourierTransform w ξ*
        sampledProjectedFourier m B (j*(q : ℕ)) J g (fun i => a i*additivePhase (ξ*x i)) r*
        sampledProjectedFourier m B (j*(q : ℕ)) K h (fun i => b i*additivePhase (-ξ*y i)) (-r)
      else 0)

theorem sampledLogKernel_residue_weights {m B d : ℕ} [NeZero d]
    (hm : 0 < m) (hB : 0 < B) (hd : d ≤ auxiliaryCutoff B)
    (J K : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (a b : Fin (channelFineCount m B) → ℂ)
    (x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ)) :
    (∑ i ∈ J, ∑ k ∈ K,
      ((channelMesh (channelFineCount m B) : ℂ)*
        (finiteResidueAverage (fun r => manuscriptChannel m B d g (i,r)) : ℂ)*a i)*
      ((channelMesh (channelFineCount m B) : ℂ)*
        (finiteResidueAverage (fun r => manuscriptChannel m B d h (k,r)) : ℂ)*b k)*
      (w (x i-y k) : ℂ)) = sampledLogKernel m B J K g h a b x y w := by
  unfold sampledLogKernel
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro k _
  rw [← Complex.ofReal_mul,manuscript_residue_average_mass hm hB hd,
    ← Complex.ofReal_mul,manuscript_residue_average_mass hm hB hd]

theorem sampledMajorKernel_eq {m B j Q : ℕ} [NeZero j]
    (hm : 0 < m) (hB : 0 < B) (hcut : j*Q ≤ auxiliaryCutoff B)
    (J K : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (a b : Fin (channelFineCount m B) → ℂ)
    (x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ)) :
    sampledMajorKernel m B j Q J K g h a b x y w =
      (((j : ℝ)/j.totient*(∑ q ∈ positiveDenominators Q,
        singularSeriesCoefficient j (q : ℕ)) : ℝ) : ℂ)*
        sampledLogKernel m B J K g h a b x y w := by
  unfold sampledMajorKernel
  have he (q : ℕ+) (hq : q ∈ positiveDenominators Q) :
      ((μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))*(∑ r : ZMod (j*(q : ℕ)),
        if r.val.Coprime (q : ℕ) then
          ∫ ξ : ℝ, testFourierTransform w ξ*
            sampledProjectedFourier m B (j*(q : ℕ)) J g (fun i => a i*additivePhase (ξ*x i)) r*
            sampledProjectedFourier m B (j*(q : ℕ)) K h (fun i => b i*additivePhase (-ξ*y i)) (-r)
        else 0) =
      (((j : ℝ)/j.totient*singularSeriesCoefficient j (q : ℕ) : ℝ) : ℂ)*
        sampledLogKernel m B J K g h a b x y w := by
    have hd : j*(q : ℕ) ≤ auxiliaryCutoff B :=
      (Nat.mul_le_mul_left j ((mem_positiveDenominators Q q).mp hq)).trans hcut
    exact (sampledProjectedFourier_kernel m B j (q : ℕ) J K g h a b x y w).trans
      (congrArg (fun z : ℂ =>
        (((j : ℝ)/j.totient*singularSeriesCoefficient j (q : ℕ) : ℝ) : ℂ)*z)
        (sampledLogKernel_residue_weights hm hB hd J K g h a b x y w))
  rw [sum_congr rfl he]
  push_cast
  rw [mul_sum,sum_mul]

theorem sampledMajorKernel_singularSeries_error
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {m B j Q : ℕ} [NeZero j]
    (hm : 0 < m) (hB : 0 < B) (hcut : j*Q ≤ auxiliaryCutoff B)
    (J K : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (a b : Fin (channelFineCount m B) → ℂ)
    (x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ)) :
    ‖sampledMajorKernel m B j Q J K g h a b x y w-
      (singularSeries j : ℂ)*sampledLogKernel m B J K g h a b x y w‖ ≤
      ((j : ℝ)/j.totient)*singularSeriesTail (Q+1)*
        ‖sampledLogKernel m B J K g h a b x y w‖ := by
  rw [sampledMajorKernel_eq hm hB hcut,← sub_mul,norm_mul,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (singularSeries_positive_truncation_error hMP j Q)
    (norm_nonneg _)

end JointDickman

end OAI
