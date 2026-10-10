import OAI.NumberTheory.Ostmann.Construction.InitialMovingTemplateProduct
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeLiveCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalLeafMultiplier

namespace OAI

/-! # The full harmonic diagonal cost for the genuine initial weights -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingAmplitude_initial_full_harmonic_cost {J : Type}
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (hμ0 : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (n a : ℕ) (hlen : 4 + a + 4 * n = r + r)
    (Q : MovingRegularSlot n a (b + b) → Finset ℕ)
    (hidentical : ∀ j k : TreeLeafIndex n × Fin (b + b),
      primeSubsetPrior P (Q (movingTemplateBulk n a (b + b) j)) =
        primeSubsetPrior P (Q (movingTemplateBulk n a (b + b) k)))
    (hvg : ∀ p : Pg, smoothGiantPrior Pg φ (G (n + 1)) p ≠ 0 → V n < (p : ℕ))
    (hvr : ∀ i (p : P), primeSubsetPrior P (Q i) p ≠ 0 → V n < (p : ℕ))
    (hsep : ∀ p : Pg, smoothGiantPrior Pg φ (G (n + 1)) p ≠ 0 →
      ∀ i (z : P), primeSubsetPrior P (Q i) z ≠ 0 → (p : ℕ) ≠ (z : ℕ))
    (Gmin : ℝ) (hX : ∀ p : Pg, smoothGiantPrior Pg φ (G (n + 1)) p ≠ 0 →
      Real.exp Gmin ≤ (p : ℝ))
    (lower : TreeLeafIndex n × Fin a → ℝ)
    (hlower : ∀ j : TreeLeafIndex n × Fin a, ∀ p : P,
      primeSubsetPrior P (Q (j.1, .inl j.2)) p ≠ 0 → Real.exp (lower j) ≤ (p : ℝ))
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    let F := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback) g Dq S ψ X lo hi
    let K := Real.exp (smoothGiantLogNormalizer Pg φ (G (n + 1)) - Gmin -
      ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2))) *
      ((Fintype.card (MovingRegularSlot n a (b + b))).factorial : ℝ) *
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹)
    movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V F φ G n a (b + b)
      Pg I (smoothGiantPrior Pg φ (G (n + 1))) (fun i => primeSubsetPrior P (Q i))
      greg ggiant favorable ≤
    K * movingAmplitudeSymmetrizedRegularEnergy P Pg I outside μ childBound pivotBound V F φ G
      n a (b + b) Q greg := by
  intro F K
  have hF (x) : F x 0 = 0 := movingOriginalLeaf_zero Subtype.val q
    (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
    (fun _ => initialMovingDataCutoff_zero Subtype.val b d r cb cd sl sr fallback _)
    g Dq S ψ X lo hi x
  apply movingAmplitude_symmetrized_full_harmonic_cost_live P Pg I hP hPg outside μ hμ0
    childBound pivotBound V F hF φ hφ0 hφ1 G n a (b + b) Q hidentical hvg hvr hsep Gmin hX
    ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) _ greg ggiant favorable
  intro u _ z hz p hp
  exact movingSymmetrizedTemplateCoefficient_original_initial_full_lower Subtype.val
    (fun p => (hP _ p.property).pos) b d r cb cd sl sr fallback q g Dq S ψ X lo hi
    outside μ childBound pivotBound V φ G n a z.2.2.val u z.2.1 hlen lower
    (fun j => hlower j _ (hz _)) p z.1 hp

end Ostmann

end OAI
