import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingSplit
import OAI.NumberTheory.Ostmann.Characters.TemplatePivotResidue

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
private theorem norm_mul_le_one {a b : ℝ} (ha : a≤1) (hb0 : 0≤b) (hb : b≤1) : a*b≤1 :=
  (mul_le_mul ha hb hb0 zero_le_one).trans_eq (one_mul 1)

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem norm_indexedFixedPhase_le_one (D : I → I → ℤ) (p : I → ℕ)
    (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I)
    (hp : ∀ i ∈ frozenVertices L S, (p i).Prime)
    (hν : ∀ i ∈ frozenVertices L S, ‖ν i (p i)‖ ≤ 1) :
    ‖indexedFixedPhase D p χ ν L S‖ ≤ 1 := by
  rw [indexedFixedPhase,norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
  intro i hi
  rw [norm_mul]
  apply norm_mul_le_one (hν i hi) (norm_nonneg _)
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun h _ => norm_nonneg _)
  intro h hh
  exact norm_character_power_le_of_prime (hp i hi) (χ i (p i)) (p h) (D i h)

theorem norm_indexedLongUnary_le_one (D : I → I → ℤ) (p : I → ℕ)
    (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I)
    (hp : ∀ i ∈ frozenVertices L S, (p i).Prime)
    (hν : ∀ i ∈ frozenVertices L S, ‖ν i (p i)‖ ≤ 1)
    (q : ℕ) (hq : q.Prime) (hνq : ‖ν L q‖ ≤ 1) :
    ‖indexedLongUnary D p χ ν L S q‖ ≤ 1 := by
  have hrow : ‖∏ h ∈ frozenVertices L S, χ L q (p h) ^ D L h‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun h _ => norm_nonneg _)
    intro h hh
    exact norm_character_power_le_of_prime hq (χ L q) (p h) (D L h)
  have hcol : ‖∏ i ∈ frozenVertices L S, χ i (p i) q ^ D i L‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
    intro i hi
    exact norm_character_power_le_of_prime (hp i hi) (χ i (p i)) q (D i L)
  simp only [indexedLongUnary,norm_mul]
  exact norm_mul_le_one (norm_mul_le_one (norm_mul_le_one hνq (norm_nonneg _) hrow)
    (norm_nonneg _) hcol) (norm_nonneg _) (norm_indexedFixedPhase_le_one D p χ ν L S hp hν)

theorem norm_indexedShortUnary_le_one (D : I → I → ℤ) (p : I → ℕ)
    (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I)
    (hp : ∀ i ∈ frozenVertices L S, (p i).Prime)
    (r : ℕ) (hr : r.Prime) (hνr : ‖ν S r‖ ≤ 1) :
    ‖indexedShortUnary D p χ ν L S r‖ ≤ 1 := by
  have hrow : ‖∏ h ∈ frozenVertices L S, χ S r (p h) ^ D S h‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun h _ => norm_nonneg _)
    intro h hh
    exact norm_character_power_le_of_prime hr (χ S r) (p h) (D S h)
  have hcol : ‖∏ i ∈ frozenVertices L S, χ i (p i) r ^ D i S‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
    intro i hi
    exact norm_character_power_le_of_prime (hp i hi) (χ i (p i)) r (D i S)
  simp only [indexedShortUnary,norm_mul]
  exact norm_mul_le_one (norm_mul_le_one hνr (norm_nonneg _) hrow) (norm_nonneg _) hcol

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
