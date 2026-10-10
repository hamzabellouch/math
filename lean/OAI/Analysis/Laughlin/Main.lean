import OAI.Analysis.Laughlin.Fock.SpectralDistance
import OAI.Analysis.Laughlin.Polynomial.PhysicalLaughlinKernel
import OAI.Analysis.Laughlin.Tensor.KernelReadout

namespace OAI

namespace Laughlin
open scoped BigOperators
open Fock

theorem distanceToLaughlinSq_le {N Q : ℕ} (ψ : State N Q) (c : ℂ) :
    distanceToLaughlinSq ψ ≤ ∑ a, ‖ψ a-c*laughlinVector N Q a‖^2 := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro t ⟨d,rfl⟩
    exact Finset.sum_nonneg (fun a ha => sq_nonneg _)
  · exact ⟨c,rfl⟩

theorem mainTarget_proved : MainTarget := by
  obtain ⟨Q₀,h25,hgap⟩ := physical_fock_kernel_distance_uniform
  refine ⟨Q₀+2,by omega,fun N hN ψ hψ => ?_⟩
  have hN2 : 2 ≤ N := by omega
  obtain ⟨n,rfl⟩ : ∃ n, N=n+2 := ⟨N-2,by omega⟩
  have hQ : Q₀ ≤ 3*(n+2-1) := by omega
  let Q := 3*(n+2-1)
  let x := normalizedTensorExterior (n+2) Q ψ
  obtain ⟨y,hy,hb⟩ := hgap Q hQ x
  have hyE : sourceFockEnergy Q y=0 := (sourceFockHamiltonian_kernel Q y).mp hy
  have hrE : energy (normalizedTensorReadout (n+2) Q y)=0 :=
    normalizedTensorReadout_zero_energy n Q y hyE
  have hrA := normalizedTensorReadout_antisymmetric (n+2) Q y
  obtain ⟨c,hc⟩ := (physical_Laughlin_kernel (show 2 ≤ n+2 by omega)
    (normalizedTensorReadout (n+2) Q y) hrA).mp hrE
  have hread : normalizedTensorReadout (n+2) Q (x-y) =
      fun a => ψ a-c*laughlinVector (n+2) Q a := by
    rw [normalizedTensorReadout_sub,normalizedTensorReadout_left_inverse (n+2) Q ψ hψ,hc]
  have hnorm := normalizedTensorReadout_norm_le (n+2) Q (x-y)
  rw [hread] at hnorm
  have hdist := distanceToLaughlinSq_le ψ c
  have hE : sourceFockEnergy Q x=energy ψ := normalizedTensorExterior_energy n Q ψ hψ
  rw [hE] at hb
  exact (mul_le_mul_of_nonneg_left (hdist.trans hnorm) (by norm_num : (0 : ℝ) ≤ 1/100)).trans hb

end Laughlin

end OAI
