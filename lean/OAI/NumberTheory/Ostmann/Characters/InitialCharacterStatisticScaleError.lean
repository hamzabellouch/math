import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleSourceError

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.InitialCharacterScale
open Construction Preliminaries Filter

theorem actual_repeated_error_small_eventually {ρ c₀ C H N A BD : ℝ}
    (hρ : 0 < ρ) (hc₀ : 0 < c₀) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hBD : gapThreshold A ρ (2*C) H ≤ BD) (k : ℕ) (hNz : N ≤ depthScale k)
    (D DH : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (Q b n : ℕ), (n : ℝ) ≤ N → b = wordSize k L+1+n →
      ∀ E : Fin b → Finset (PrimeUpTo Q), (∀ i, 0 < primeShellMass (E i)) →
      ∀ X M₀ : ℝ, 0 < X →
      (∏ i, (primeShellMass (E i))⁻¹) ≤
        (1/(ρ*L))^(wordSize k L)/c₀*Real.exp (C*N*L) →
      primeShellMass (Finset.univ.biUnion E) ≤ H*L+DH →
      X*Real.exp (initialGap BD k L-D) ≤ M₀ →
      initialCharacterRepeatedError E X M₀ ≤ (1/2)*Real.exp (-A*(wordSize k L : ℝ)) := by
  have hK : 0 ≤ sourceErrorConstant c₀ C D DH := by
    unfold sourceErrorConstant
    positivity
  filter_upwards [repeated_scalar_absorption hρ (by positivity : 0 ≤ 2*C) hH hK hBD
    k (2+2*⌈N⌉₊),eventually_gt_atTop (0 : ℝ)] with L hscalar hL
  intro Q b n hn hb E hE X M₀ hX hNorm hUnion hM
  have hnceil : n ≤ ⌈N⌉₊ := by exact_mod_cast hn.trans (Nat.le_ceil N)
  have hbound := source_error_bound E hE hρ hc₀ hC hL hX k hNz hNorm hUnion hM
  have hcount : b+b=2*wordSize k L+(2+2*n) := by omega
  rw [hcount] at hbound
  exact hbound.trans (hscalar (2+2*n) (by omega))

end Ostmann.Characters.InitialCharacterScale

end

end OAI
