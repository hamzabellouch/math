import OAI.Probability.RandomSAT.Replacement

namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def uniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

theorem uniformMean_congr {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a = g a) : uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c := by
  simp [uniformMean, ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos :
    (0 : ℝ) < Fintype.card α)]

theorem uniformMean_zero {α : Type*} [Fintype α] :
    uniformMean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [uniformMean]

theorem uniformMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

theorem uniformMean_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    uniformMean (fun a => f a * c) = uniformMean f * c := by
  simp only [uniformMean, ← Finset.sum_mul]
  ring

theorem uniformMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

theorem uniformMean_sum {α ι : Type*} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    uniformMean (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem uniformMean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformMean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) : uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  simp only [uniformMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

theorem uniformMean_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) := by
  simp only [uniformMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem uniformProbability_eq_mean {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p = uniformMean (fun a => if p a then 1 else 0) := by
  classical
  unfold uniformProbability uniformMean
  congr 1
  simp [Fintype.card_subtype]

theorem uniformMean_sq_sub {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (c : ℝ) :
    uniformMean (fun a => (f a - c)^2) =
      uniformMean (fun a => f a ^ 2) - 2 * c * uniformMean f + c^2 := by
  calc
    _ = uniformMean (fun a => (f a ^ 2 - (2 * c) * f a) + c^2) :=
      uniformMean_congr (fun _ => by ring)
    _ = _ := by rw [uniformMean_add, uniformMean_sub, uniformMean_const_mul, uniformMean_const]

theorem uniformMean_sq_ge {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : uniformMean f ^ 2 ≤ uniformMean (fun a => f a ^ 2) := by
  have h := uniformMean_nonneg (fun a => sq_nonneg (f a - uniformMean f))
  rw [uniformMean_sq_sub] at h
  nlinarith

def uniformVariance {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  uniformMean (fun a => (f a - uniformMean f)^2)

theorem uniformVariance_eq {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : uniformVariance f = uniformMean (fun a => f a^2) - uniformMean f ^ 2 := by
  rw [uniformVariance, uniformMean_sq_sub]
  ring

theorem uniformVariance_le_sq_dist {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (c : ℝ) : uniformVariance f ≤ uniformMean (fun a => (f a - c)^2) := by
  rw [uniformVariance_eq, uniformMean_sq_sub]
  nlinarith [sq_nonneg (uniformMean f - c)]

end


end FixedClauseThreshold

end OAI
