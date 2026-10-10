import OAI.Geometry.HeilbronnTriangle.ConditionalSamples
import OAI.Geometry.HeilbronnTriangle.ConditionalMatrix

namespace OAI


namespace Problem355.DigitColumnLaw

noncomputable section
open scoped BigOperators

abbrev Column (X : Type*) (k : ℕ) := Fin 3 → Fin k → X
abbrev Latent (Λ X : Type*) (k : ℕ) := Λ × Column X k
abbrev Array (X : Type*) (k : ℕ) := Fin 3 → Fin 3 → Fin k → X

def uniformWeight (α : Type*) [Fintype α] (_ : α) : ℝ := 1 / Fintype.card α

lemma uniformWeight_nonneg (α : Type*) [Fintype α] (a : α) :
    0 ≤ uniformWeight α a := by unfold uniformWeight; positivity

lemma sum_uniformWeight (α : Type*) [Fintype α] [Nonempty α] :
    ∑ a : α, uniformWeight α a = 1 := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  simp only [uniformWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_one_div_cancel hcard.ne'

lemma productWeight_uniform {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (s : ι → α) :
    ConditionalSamples.productWeight (uniformWeight α) s = uniformWeight (ι → α) s := by
  simp [ConditionalSamples.productWeight, uniformWeight]

def tripleEquiv {Λ X : Type*} {k : ℕ} :
    (Fin 3 → Latent Λ X k) ≃ ((Fin 3 → Λ) × Array X k) where
  toFun s := (fun c => (s c).1, fun a c v => (s c).2 a v)
  invFun t := fun c => (t.1 c, fun a v => t.2 a c v)
  left_inv s := by funext c; rfl
  right_inv t := by cases t; rfl

theorem expectation_triple {Λ X : Type*} [Fintype Λ] [Fintype X] {k : ℕ}
    (F : (Fin 3 → Λ) → Array X k → ℝ) :
    (∑ s : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) s *
        F (tripleEquiv s).1 (tripleEquiv s).2) =
      ∑ labels : Fin 3 → Λ, uniformWeight (Fin 3 → Λ) labels *
        ∑ f : Array X k, uniformWeight (Array X k) f * F labels f := by
  simp_rw [productWeight_uniform]
  have hcard := Fintype.card_congr (tripleEquiv (Λ := Λ) (X := X) (k := k))
  have hsum := (tripleEquiv (Λ := Λ) (X := X) (k := k)).sum_comp
    (fun t => (1 / (Fintype.card (Fin 3 → Latent Λ X k) : ℝ)) * F t.1 t.2)
  change (∑ s : Fin 3 → Latent Λ X k,
    (1 / (Fintype.card (Fin 3 → Latent Λ X k) : ℝ)) *
      F (tripleEquiv s).1 (tripleEquiv s).2) = _
  rw [hsum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro labels _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [hcard]
  simp only [uniformWeight, Fintype.card_prod, Nat.cast_mul, one_div, mul_inv_rev]
  ring

theorem expectation_triple_le {Λ X : Type*} [Fintype Λ] [Nonempty Λ] [Fintype X] {k : ℕ}
    (F : (Fin 3 → Λ) → Array X k → ℝ) (M : ℝ)
    (hF : ∀ labels, (∑ f : Array X k, uniformWeight (Array X k) f * F labels f) ≤ M) :
    (∑ s : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) s *
        F (tripleEquiv s).1 (tripleEquiv s).2) ≤ M := by
  rw [expectation_triple]
  calc
    _ ≤ ∑ labels : Fin 3 → Λ, uniformWeight (Fin 3 → Λ) labels * M := by
      apply Finset.sum_le_sum
      intro labels _
      exact mul_le_mul_of_nonneg_left (hF labels) (uniformWeight_nonneg _ labels)
    _ = M := by rw [← Finset.sum_mul, sum_uniformWeight, one_mul]

def residueColumn {Λ X : Type*} {B k : ℕ}
    (digit : Λ → Fin 3 → Fin k → X → Fin B)
    (x : Latent Λ X k) : Fin 3 → ZMod (B ^ k) :=
  fun a => ((∑ v : Fin k, (digit x.1 a v (x.2 a v)).val * B ^ v.val : ℕ) : ZMod (B ^ k))

theorem residueColumn_matrix {Λ X : Type*} {B k : ℕ}
    (digit : Λ → Fin 3 → Fin k → X → Fin B) (s : Fin 3 → Latent Λ X k) :
    (fun a c => residueColumn digit (s c) a) =
      ConditionalMatrix.arrayMatrix
        (fun a c v x => digit ((tripleEquiv s).1 c) a v x) (tripleEquiv s).2 k := rfl

end
end Problem355.DigitColumnLaw

end OAI
