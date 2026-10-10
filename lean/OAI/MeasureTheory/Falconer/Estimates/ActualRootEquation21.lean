import OAI.MeasureTheory.Falconer.Estimates.RootEquation21
import OAI.MeasureTheory.Falconer.Estimates.RootSupremum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace RootShellData

theorem uniform_equation21 {sig δ L eps T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) (hL : 0 < L) (heps : 0 < eps) :
    ∃ n N₀ : ℕ, ∀ d : RootShellData,
    ∀ [IsProbabilityMeasure d.left.ρ] [IsProbabilityMeasure d.right.ρ],
    N₀ ≤ d.N → d.sig = sig → 0 < d.left.Q.side → 0 < d.right.Q.side →
    d.left.S.card ≤ (d.N+1)^3+1 → d.right.S.card ≤ (d.N+1)^3+1 →
    (∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2) →
    (∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2) →
    0 < d.U.side → 0 < d.V.side →
    (∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) → (∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier) →
    (∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) →
    ∀ s : ℝ, d.U.side ≤ s → d.V.side ≤ s → 100*s ≤ dist d.U.center d.V.center →
    ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
    (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
    ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) → (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
    (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
      ((2:ℝ)^d.N)^eps*d.inverseShellSupremum n d.N Ψ+((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_parent_bound (T := T) hsig hsmall hδ hL heps
  refine ⟨n,N₀,?_⟩
  intro d inst₁ inst₂ hN hsigd hd he hc₁ hc₂ hl₁ hl₂ hU hV hcarry₁ hcarry₂ hsep s hUs hVs hstrong Ψ hΨ hpos hs W hW hΨW hone
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hsup := d.inverseShellSupremum_majorizes hd he n d.N Ψ hW hΨW hsupport
  exact h₀ d hN hsigd hd he hc₁ hc₂ hl₁ hl₂ hU hV hcarry₁ hcarry₂ hsep s hUs hVs hstrong
    Ψ hΨ hpos hs W hW hΨW hone _ hsup.1 hsup.2

end RootShellData

end PlanarFalconer

end OAI
