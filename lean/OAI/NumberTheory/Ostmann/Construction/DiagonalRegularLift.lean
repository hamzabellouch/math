import OAI.NumberTheory.Ostmann.Construction.ExternalResidueReduction
import OAI.NumberTheory.Ostmann.Construction.DiagonalRegularMultiplier

namespace OAI

/-! # Regular-prime cancellation from the full higher-power modulus -/

namespace Ostmann
open scoped BigOperators Classical

/-- Extra powers introduced when clearing the moving denominators have no
cost when the signed integrand factors through the displayed CRT coordinates. -/
theorem diagonalRegularMultiplier_full_modulus {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (M : ℕ) [NeZero M] (hd : (∏ i, p i) * r ∣ M)
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i))
    (hs : ∀ i, (s : ZMod (p i)) ≠ 0) (ho : ∀ i, other i ≠ 0)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (F : ZMod r × (ZMod r)ˣ → ℂ) :
    (Fintype.card (ZMod M × (ZMod M)ˣ) : ℂ)⁻¹ *
      (∑ z, (diagonalRegularMultiplier p active s other g
        (crtExternalPairEquiv p hc
          (crtSplitExternalEquiv (∏ i, p i) r hcop (externalResidueReduction hd z)).1) : ℂ) *
        F (crtSplitExternalEquiv (∏ i, p i) r hcop (externalResidueReduction hd z)).2) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ∑ z, F z) := by
  rw [uniform_external_residue_reduction hd (fun z =>
    (diagonalRegularMultiplier p active s other g
      (crtExternalPairEquiv p hc (crtSplitExternalEquiv (∏ i, p i) r hcop z).1) : ℂ) *
      F (crtSplitExternalEquiv (∏ i, p i) r hcop z).2)]
  exact diagonalRegularMultiplier_crt p hc r hcop active s other hs ho g hg henergy F

end Ostmann

end OAI
