import OAI.NumberTheory.Ostmann.Construction.RegularDiagonalCancellation

namespace OAI

/-! # Removing the regular-prime block from the signed arithmetic average -/

namespace Ostmann

open scoped BigOperators

/-- Simultaneously split the integer and unit giant residues. -/
noncomputable def crtSplitExternalEquiv (c r : ℕ) (hc : c.Coprime r) :
    (ZMod (c * r) × (ZMod (c * r))ˣ) ≃
      (ZMod c × (ZMod c)ˣ) × (ZMod r × (ZMod r)ˣ) :=
  ((ZMod.chineseRemainder hc).toEquiv.prodCongr (crtSplitUnitEquiv c r hc)).trans
    (Equiv.prodProdProdComm _ _ _ _)

/-- The signed remainder includes spectator, internal-prime and frequency
tests, including the retained Page correction. No absolute value is taken. -/
theorem crt_external_regular_with_remainder {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)]
    (hcop : (∏ i, p i).Coprime r)
    (active : I → Bool) (a : ∀ i, (ZMod (p i))ˣ) (g : ∀ i, ZMod (p i) → ℂ)
    (hg : ∀ i, g i 0 = 0) (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (F : ZMod r × (ZMod r)ˣ → ℂ) :
    (Fintype.card (ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ) : ℂ)⁻¹ *
      (∑ z,
        ((∏ i, externalRegularLocal (active i) (a i) (g i)
          (crtExternalPairEquiv p hc (crtSplitExternalEquiv (∏ i, p i) r hcop z).1 i) : ℝ) : ℂ) *
        F (crtSplitExternalEquiv (∏ i, p i) r hcop z).2) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ∑ z, F z) := by
  have hreg := crt_external_regular_cancellation p hc active a g hg henergy
  have hregC : (Fintype.card (ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) : ℂ)⁻¹ *
      (∑ z, ((∏ i, externalRegularLocal (active i) (a i) (g i)
        (crtExternalPairEquiv p hc z i) : ℝ) : ℂ)) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_sum] using congrArg (fun t : ℝ => (t : ℂ)) hreg
  rw [uniform_equiv_product_average (crtSplitExternalEquiv (∏ i, p i) r hcop)
    (fun z => ((∏ i, externalRegularLocal (active i) (a i) (g i)
      (crtExternalPairEquiv p hc z i) : ℝ) : ℂ)) F, hregC]

end Ostmann

end OAI
