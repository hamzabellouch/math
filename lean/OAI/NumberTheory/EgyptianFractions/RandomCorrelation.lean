import OAI.NumberTheory.EgyptianFractions.FiniteExposureAverage
import OAI.NumberTheory.EgyptianFractions.ExposedCorrelation

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.RandomProducts

/-- Transfer an exposed product factorization to a pair-correlation estimate.
The bad-exposure counting and the fresh-product cancellation are separate,
explicit inputs, so this lemma does not assume probabilistic independence. -/
theorem correlation_of_exposed_products
    {Ω E A B : Type*} [Fintype Ω] [Fintype E] [Fintype A] [Fintype B]
    [Nonempty E] [Nonempty A] [Nonempty B]
    (e : Ω ≃ E × (A × B)) (pI pJ : Ω → ℕ)
    (U V : E → ℕ) (f : A → ℕ) (g : B → ℕ)
    (hI : ∀ c a b, pI (e.symm (c, (a, b))) = U c * f a * g b)
    (hJ : ∀ c a b, pJ (e.symm (c, (a, b))) = V c)
    (u l : ℕ) [NeZero u] (bad : Finset E) (ε δ : ℝ) (hδ : 0 ≤ δ)
    (hbad : (bad.card : ℝ) / Fintype.card E ≤ ε)
    (hgood : ∀ c, c ∉ bad →
      ‖𝔼 a : A, 𝔼 b : B,
        ZMod.stdAddChar (((l * U c * f a * g b : ℕ) : ZMod u) -
          ((l * V c : ℕ) : ZMod u))‖ ≤ δ) :
    ‖𝔼 ω : Ω, ZMod.stdAddChar (((l * pI ω : ℕ) : ZMod u) -
      ((l * pJ ω : ℕ) : ZMod u))‖ ≤ ε + δ := by
  have h := exposure_average_norm_bound e
    (fun ω : Ω => ZMod.stdAddChar (((l * pI ω : ℕ) : ZMod u) -
      ((l * pJ ω : ℕ) : ZMod u))) bad δ hδ
    (fun ω => (AddChar.norm_apply _ _).le) ?_
  · exact h.trans (by linarith)
  · intro c hc
    rw [show (𝔼 ab : A × B,
        ZMod.stdAddChar (((l * pI (e.symm (c, ab)) : ℕ) : ZMod u) -
          ((l * pJ (e.symm (c, ab)) : ℕ) : ZMod u))) =
        𝔼 a : A, 𝔼 b : B,
          ZMod.stdAddChar (((l * pI (e.symm (c, (a,b))) : ℕ) : ZMod u) -
            ((l * pJ (e.symm (c, (a,b))) : ℕ) : ZMod u)) by
      exact Finset.expect_product Finset.univ Finset.univ _]
    simp_rw [hI, hJ, ← Nat.mul_assoc]
    exact hgood c hc

end Problem337.RandomProducts

end

end OAI
