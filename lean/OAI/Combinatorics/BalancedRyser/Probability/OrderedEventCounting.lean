import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace OAI

namespace Balanced.OrderedEventCounting

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in

theorem reorder_injective {b : ℕ} (f : Fin b → ι) (hf : Function.Injective f) :
    Function.Injective (fun σ : Equiv.Perm (Fin b) => f ∘ σ) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  exact hf (congrFun h i)

theorem factorial_le_card_orders {b : ℕ} (R : (Fin b → ι) → Prop)
    (f : Fin b → ι) (hf : Function.Injective f)
    (hR : ∀ σ : Equiv.Perm (Fin b), R (f ∘ σ)) :
    b.factorial ≤ Fintype.card {g : Fin b → ι // R g} := by
  classical
  let lift : Equiv.Perm (Fin b) → {g : Fin b → ι // R g} :=
    fun σ => ⟨f ∘ σ, hR σ⟩
  have hinj : Function.Injective lift := by
    intro σ τ h
    exact reorder_injective f hf (congrArg Subtype.val h)
  simpa only [Fintype.card_perm, Fintype.card_fin] using
    Fintype.card_le_of_injective lift hinj

theorem factorial_le_sum_orders {b : ℕ} (R : (Fin b → ι) → Prop)
    (f : Fin b → ι) (hf : Function.Injective f)
    (hR : ∀ σ : Equiv.Perm (Fin b), R (f ∘ σ)) :
    (b.factorial : ℝ) ≤ ∑ g : Fin b → ι, if R g then (1 : ℝ) else 0 := by
  classical
  have h := factorial_le_card_orders R f hf hR
  have hc : (Fintype.card {g : Fin b → ι // R g} : ℝ) =
      ∑ g : Fin b → ι, if R g then (1 : ℝ) else 0 := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  rw [← hc]
  exact_mod_cast h

theorem weighted_order_bound {Ω : Type*} [Fintype Ω] {b : ℕ}
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (E : Ω → Prop)
    (R : (Fin b → ι) → Ω → Prop)
    (hcover : ∀ ω, 0 < w ω → E ω →
      ∃ f : Fin b → ι, Function.Injective f ∧
        ∀ σ : Equiv.Perm (Fin b), R (f ∘ σ) ω) :
    (∑ ω, if E ω then w ω else 0) ≤
      (∑ g : Fin b → ι, ∑ ω, if R g ω then w ω else 0) / (b.factorial : ℝ) := by
  classical
  have hb : (0 : ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  apply (le_div_iff₀ hb).mpr
  rw [Finset.sum_mul, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : 0 < w ω
  · by_cases he : E ω
    · obtain ⟨f, hf, hR⟩ := hcover ω hp he
      have hcount := factorial_le_sum_orders (fun g => R g ω) f hf hR
      calc
        (if E ω then w ω else 0) * (b.factorial : ℝ) =
            (b.factorial : ℝ) * w ω := by rw [ite_eq_left he, mul_comm]
        _ ≤ (∑ g : Fin b → ι, if R g ω then (1 : ℝ) else 0) * w ω :=
          mul_le_mul_of_nonneg_right hcount (hw ω)
        _ = ∑ g : Fin b → ι, if R g ω then w ω else 0 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro g _
          split_ifs <;> simp
    · simp only [ite_eq_right he, zero_mul]
      exact Finset.sum_nonneg (fun g _ => by split_ifs <;> simp_all)
  · have hz : w ω = 0 := le_antisymm (le_of_not_gt hp) (hw ω)
    simp only [hz, ite_self, zero_mul, Finset.sum_const_zero, le_refl]

omit [Fintype ι] in

theorem factorial_le_sum_encoded_orders {J : Type*} [Fintype J] {b : ℕ}
    (R : J → Prop) (read : J → Fin b → ι)
    (f : Fin b → ι) (hf : Function.Injective f)
    (hR : ∀ σ : Equiv.Perm (Fin b), ∃ j, R j ∧ read j = f ∘ σ) :
    (b.factorial : ℝ) ≤ ∑ j, if R j then (1 : ℝ) else 0 := by
  classical
  choose pick hpick hread using hR
  let lift : Equiv.Perm (Fin b) → {j // R j} := fun σ => ⟨pick σ, hpick σ⟩
  have hi : Function.Injective lift := by
    intro σ τ h
    apply reorder_injective f hf
    change f ∘ σ = f ∘ τ
    rw [← hread σ, ← hread τ]
    exact congrArg read (congrArg Subtype.val h)
  have hc : b.factorial ≤ Fintype.card {j // R j} := by
    simpa only [Fintype.card_perm, Fintype.card_fin] using
      Fintype.card_le_of_injective lift hi
  have he : (Fintype.card {j // R j} : ℝ) =
      ∑ j, if R j then (1 : ℝ) else 0 := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  rw [← he]
  exact_mod_cast hc

omit [Fintype ι] in

theorem weighted_encoded_order_bound {Ω J : Type*} [Fintype Ω] [Fintype J] {b : ℕ}
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (E : Ω → Prop)
    (R : J → Ω → Prop) (read : J → Fin b → ι)
    (hcover : ∀ ω, 0 < w ω → E ω →
      ∃ f : Fin b → ι, Function.Injective f ∧
        ∀ σ : Equiv.Perm (Fin b), ∃ j, R j ω ∧ read j = f ∘ σ) :
    (∑ ω, if E ω then w ω else 0) ≤
      (∑ j, ∑ ω, if R j ω then w ω else 0) / (b.factorial : ℝ) := by
  classical
  have hb : (0 : ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  apply (le_div_iff₀ hb).mpr
  rw [Finset.sum_mul, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : 0 < w ω
  · by_cases he : E ω
    · obtain ⟨f, hf, hR⟩ := hcover ω hp he
      have hcount := factorial_le_sum_encoded_orders (fun j => R j ω) read f hf hR
      calc
        (if E ω then w ω else 0) * (b.factorial : ℝ) =
            (b.factorial : ℝ) * w ω := by rw [ite_eq_left he, mul_comm]
        _ ≤ (∑ j, if R j ω then (1 : ℝ) else 0) * w ω :=
          mul_le_mul_of_nonneg_right hcount (hw ω)
        _ = ∑ j, if R j ω then w ω else 0 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> simp
    · simp only [ite_eq_right he, zero_mul]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp_all)
  · have hz : w ω = 0 := le_antisymm (le_of_not_gt hp) (hw ω)
    simp only [hz, ite_self, zero_mul, Finset.sum_const_zero, le_refl]

end
end Balanced.OrderedEventCounting

end OAI
