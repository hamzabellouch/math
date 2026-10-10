import OAI.Analysis.Laughlin.GapEstimates
import OAI.Analysis.Laughlin.Charge.LaughlinGround
import OAI.Analysis.Laughlin.Charge.Overlap

namespace OAI

namespace Laughlin
open Fock

theorem uniform_fock_gap (γ : ℝ) (_hγ0 : 0<γ) (hγ : γ<gammaStar) :
    ∃ Q₀ : ℕ, 25≤Q₀ ∧ ∀ Q : ℕ, Q₀≤Q → ∀ x : Space Q,
      γ*sourceFockEnergy Q x≤occupationNormSq Q (sourceFockHamiltonian Q x) :=
  physical_fock_square_uniform_sharp γ hγ

theorem sharpMainTarget_proved : SharpMainTarget :=
  sharpMainTarget_of_haldane haldaneKernelInput

theorem charge_neutral_gap :
    (∀ n : ℕ, 2≤n →
      Charge.chargeGap (3*(n-1)) n=Charge.groundEnergy (3*(n-1)) (n+1) ∧
      0<Charge.neutralGap (3*(n-1)) n ∧
      (n : ℝ)*Charge.neutralGap (3*(n-1)) n/((n : ℝ)-1)≤Charge.chargeGap (3*(n-1)) n ∧
      0<Charge.chargeGap (3*(n-1)) n) ∧
    (∃ n₀ : ℕ, 2≤n₀ ∧ ∀ n : ℕ, n₀≤n →
      (n : ℝ)/(25*((n : ℝ)-1))≤Charge.chargeGap (3*(n-1)) n) :=
  Charge.charge_neutral_full_of_published Charge.lnwyRecursionInput
    Charge.lnwyRankOneInput Charge.laughlinChargeGroundInput

theorem planar_gap {N : ℕ} (ψ : Planar.HomogeneousState N) :
    ENNReal.ofReal gammaStar * Planar.fullEnergy ψ≤Planar.fullSquareNorm ψ :=
  Planar.full_planar_endpoint ψ

end Laughlin

end OAI
