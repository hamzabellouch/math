import OAI.MeasureTheory.Falconer.Shells.HighShellEquation21
import OAI.MeasureTheory.Falconer.Shells.HighShellSupremum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem uniform_high_shell_equation21 {sig lam eps T : ℝ}
    (hsig : 0 < sig) (heps : 0 < eps) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, ∀ (B : ℕ) (δ : ℝ),
    RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    N₀ ≤ d.N → d.sig = sig → d.lam = lam →
    0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    d.X.length = d.a → d.Y.length = d.a →
    ∀ v : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → v ≤ d.t →
    ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
    (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
    ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) →
    (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖charFun d.weightedDistance r‖^2) ≤
        ((2:ℝ)^d.N)^eps*d.inverseShellSupremum n v Ψ+((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_high_shell_parent_bound (lam := lam) (T := T) hsig heps
  refine ⟨n,N₀,?_⟩
  intro d B δ hd hN hdSig hdLam hQ hsep hq hqs hw ht hX hY v hv hvt Ψ hΨ hpos hs W hW hΨW hone
  let := hd.probability
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hsup := d.inverseShellSupremum_majorizes hQ n v Ψ hW hΨW hsupport
  exact h₀ d B δ hd hN hdSig hdLam hQ hsep hq hqs hw ht hX hY v hv hvt
    Ψ hΨ hpos hs W hW hΨW hone _ hsup.1 hsup.2

end PositiveDistanceData

end PlanarFalconer

end OAI
