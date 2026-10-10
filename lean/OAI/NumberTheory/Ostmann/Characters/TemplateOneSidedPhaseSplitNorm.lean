import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSplit
import OAI.NumberTheory.Ostmann.Characters.TemplatePivotResidue

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem norm_character_power_le_of_prime {q : ℕ} (hq : q.Prime)
    (χ : MulChar (ZMod q) ℂ) (n : ℕ) (e : ℤ) : ‖χ n ^ e‖ ≤ 1 := by
  let : Fact q.Prime := ⟨hq⟩
  exact norm_character_zpow_le_one χ n e

theorem norm_fixedPhase_le_one (D : I → I → ℤ) (p : I → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I)
    (hp : ∀ i ∈ frozenVertices L S, (p i).Prime)
    (hν : ∀ i ∈ frozenVertices L S, ‖ν i (p i)‖ ≤ 1) :
    ‖fixedPhase D p χ ν L S‖ ≤ 1 := by
  rw [fixedPhase,norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
  intro i hi
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (hν i hi)).trans
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun h _ => norm_nonneg _)
  intro h hh
  exact norm_character_power_le_of_prime (hp i hi) (χ (p i)) (p h) (D i h)

theorem norm_longUnary_le_one (D : I → I → ℤ) (p : I → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I)
    (hp : ∀ i ∈ frozenVertices L S, (p i).Prime)
    (hν : ∀ i ∈ frozenVertices L S, ‖ν i (p i)‖ ≤ 1)
    (q : ℕ) (hq : q.Prime) (hνq : ‖ν L q‖ ≤ 1) :
    ‖longUnary D p χ ν L S q‖ ≤ 1 := by
  have hrow : ‖∏ h ∈ frozenVertices L S, χ q (p h) ^ D L h‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun h _ => norm_nonneg _)
    intro h hh
    exact norm_character_power_le_of_prime hq (χ q) (p h) (D L h)
  have hcol : ‖∏ i ∈ frozenVertices L S, χ (p i) q ^ D i L‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
    intro i hi
    exact norm_character_power_le_of_prime (hp i hi) (χ (p i)) q (D i L)
  simp only [longUnary,norm_mul]
  have hνrow := (mul_le_of_le_one_left (norm_nonneg _) hνq).trans hrow
  have hνrowcol := (mul_le_of_le_one_left (norm_nonneg _) hνrow).trans hcol
  exact (mul_le_of_le_one_left (norm_nonneg _) hνrowcol).trans
    (norm_fixedPhase_le_one D p χ ν L S hp hν)

theorem norm_shortUnary_le_one (D : I → I → ℤ) (p : I → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I)
    (hp : ∀ i ∈ frozenVertices L S, (p i).Prime)
    (r : ℕ) (hr : r.Prime) (hνr : ‖ν S r‖ ≤ 1) :
    ‖shortUnary D p χ ν L S r‖ ≤ 1 := by
  have hrow : ‖∏ h ∈ frozenVertices L S, χ r (p h) ^ D S h‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun h _ => norm_nonneg _)
    intro h hh
    exact norm_character_power_le_of_prime hr (χ r) (p h) (D S h)
  have hcol : ‖∏ i ∈ frozenVertices L S, χ (p i) r ^ D i S‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
    intro i hi
    exact norm_character_power_le_of_prime (hp i hi) (χ (p i)) r (D i S)
  simp only [shortUnary,norm_mul]
  have hνrow := (mul_le_of_le_one_left (norm_nonneg _) hνr).trans hrow
  exact (mul_le_of_le_one_left (norm_nonneg _) hνrow).trans hcol

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
