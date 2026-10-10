import OAI.Analysis.Laughlin.Fock.SharpGap
import OAI.Analysis.Laughlin.Main

namespace OAI

namespace Laughlin
open Fock
open scoped BigOperators

def HaldaneKernelInput : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ ψ : State N (3*(N-1)), Antisymmetric ψ →
    energy ψ = 0 → ∃ c : ℂ, ψ = fun a => c * laughlinVector N (3*(N-1)) a

def SharpMainTarget : Prop :=
  ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ ψ : State N (3*(N-1)), Antisymmetric ψ →
      (1/25 : ℝ) * distanceToLaughlinSq ψ ≤ energy ψ

theorem sharpMainTarget_of_haldane (hkernel : HaldaneKernelInput) : SharpMainTarget := by
  obtain ⟨Q₀,h25,hgap⟩ := physical_fock_kernel_distance_uniform_sharp (1/25)
    (by norm_num) one_twenty_fifth_lt_gammaStar
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
  obtain ⟨c,hc⟩ := (hkernel (n+2) (show 2 ≤ n+2 by omega)
    (normalizedTensorReadout (n+2) Q y) hrA) hrE
  have hread : normalizedTensorReadout (n+2) Q (x-y) =
      fun a => ψ a-c*laughlinVector (n+2) Q a := by
    rw [normalizedTensorReadout_sub,normalizedTensorReadout_left_inverse (n+2) Q ψ hψ,hc]
  have hnorm := normalizedTensorReadout_norm_le (n+2) Q (x-y)
  rw [hread] at hnorm
  have hdist := distanceToLaughlinSq_le ψ c
  have hE : sourceFockEnergy Q x=energy ψ := normalizedTensorExterior_energy n Q ψ hψ
  rw [hE] at hb
  exact (mul_le_mul_of_nonneg_left (hdist.trans hnorm) (by norm_num : (0 : ℝ) ≤ 1/25)).trans hb

end Laughlin

end OAI
