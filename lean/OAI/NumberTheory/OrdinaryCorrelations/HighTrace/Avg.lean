import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.FiniteIntegration

variable {α β γ ι : Type*}

def avg [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ a, f a

lemma avg_nonneg [Fintype α] {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ avg f := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (sum_nonneg (fun a _ => hf a))

lemma avg_mono [Fintype α] {f g : α → ℝ} (hfg : ∀ a, f a ≤ g a) :
    avg f ≤ avg g := mul_le_mul_of_nonneg_left (sum_le_sum (fun a _ => hfg a))
      (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma avg_const [Fintype α] [Nonempty α] (c : ℝ) : avg (fun _ : α => c) = c := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg, sum_const, card_univ, nsmul_eq_mul]
  field_simp

lemma avg_mul_left [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun a => c * f a) = c * avg f := by
  simp only [avg, ← mul_sum]
  ring

lemma avg_mul_right [Fintype α] (f : α → ℝ) (c : ℝ) :
    avg (fun a => f a * c) = avg f * c := by
  simp only [avg, ← sum_mul]
  ring

lemma avg_prod [Fintype α] [Fintype β] (f : α × β → ℝ) :
    avg f = avg (fun a => avg (fun b => f (a,b))) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type]
  rw [← mul_sum]
  ring

lemma avg_product [Fintype ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (f : ∀ i, Ω i → ℝ) :
    avg (fun x : ∀ i, Ω i => ∏ i, f i (x i)) = ∏ i, avg (f i) := by
  classical
  simp only [avg, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib,
    ← Fintype.prod_sum, prod_mul_distrib]

lemma abs_avg_le [Fintype α] (f : α → ℝ) : |avg f| ≤ avg (fun a => |f a|) := by
  rw [avg, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))

def separatedKernel [Fintype α] [Fintype β] [Fintype γ]
    (cutoff : α → β → ℝ) (fixed : α → ℝ) (core : β → ℝ) (center : γ → ℝ)
    (a : α) (bc : β × γ) : ℝ :=
  cutoff a bc.1 * fixed a * core bc.1 * center bc.2

def assignedIntegral [Fintype α] [Fintype β] [Fintype γ]
    (group : α → Prop) (cutoff : α → β → ℝ) (fixed : α → ℝ)
    (core : β → ℝ) (center : γ → ℝ) : ℝ := by
  classical
  exact avg (fun a => if group a then
    |avg (separatedKernel cutoff fixed core center a)| else 0)

theorem assignedIntegral_signed [Fintype α] [Fintype β] [Fintype γ]
    (group : α → Prop) (cutoff : α → β → ℝ) (fixed : α → ℝ)
    (core : β → ℝ) (center : γ → ℝ)
    (hcutoff : ∀ a b, 0 ≤ cutoff a b) (hcore : ∀ b, 0 ≤ core b) :
    assignedIntegral group cutoff fixed core center =
      |avg center| * avg (fun a => if group a then
        |fixed a| * avg (fun b => cutoff a b * core b) else 0) := by
  classical
  have hin (a : α) :
      avg (separatedKernel cutoff fixed core center a) =
        fixed a * avg (fun b => cutoff a b * core b) * avg center := by
    rw [avg_prod]
    simp only [separatedKernel, avg_mul_left, avg_mul_right]
    congr 1
    calc
      avg (fun b => cutoff a b * fixed a * core b) =
          avg (fun b => fixed a * (cutoff a b * core b)) := by
        congr 1
        funext b
        ring
      _ = fixed a * avg (fun b => cutoff a b * core b) := avg_mul_left _ _
  have hpoint (a : α) :
      (if group a then |avg (separatedKernel cutoff fixed core center a)| else 0) =
        |avg center| * (if group a then
          |fixed a| * avg (fun b => cutoff a b * core b) else 0) := by
    split_ifs with ha
    · rw [hin, abs_mul, abs_mul, abs_of_nonneg
        (avg_nonneg (fun b => mul_nonneg (hcutoff a b) (hcore b)))]
      ring
    · ring
  unfold assignedIntegral
  simp_rw [hpoint]
  exact avg_mul_left _ _

theorem assignedIntegral_le_product [Fintype α] [Fintype β] [Fintype γ]
    (group : α → Prop) (cutoff : α → β → ℝ) (fixed : α → ℝ)
    (core : β → ℝ) (center : γ → ℝ) (M : ℝ) (u : α → ℝ) (v : β → ℝ)
    (hcutoff : ∀ a b, 0 ≤ cutoff a b) (hcore : ∀ b, 0 ≤ core b)
    (hM : 0 ≤ M) (hu : ∀ a, 0 ≤ u a) (hv : ∀ b, 0 ≤ v b)
    (hcut : ∀ a, group a → ∀ b, cutoff a b ≤ M * u a * v b) :
    assignedIntegral group cutoff fixed core center ≤
      M * |avg center| * avg (fun a => if group a then |fixed a| * u a else 0) *
        avg (fun b => v b * core b) := by
  classical
  rw [assignedIntegral_signed group cutoff fixed core center hcutoff hcore]
  calc
    _ ≤ |avg center| * avg (fun a => if group a then
          |fixed a| * (M * u a * avg (fun b => v b * core b)) else 0) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply avg_mono
      intro a
      split_ifs with ha
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc
          _ ≤ avg (fun b => (M * u a * v b) * core b) :=
            avg_mono (fun b => mul_le_mul (hcut a ha b) le_rfl (hcore b)
              (mul_nonneg (mul_nonneg hM (hu a)) (hv b)))
          _ = M * u a * avg (fun b => v b * core b) := by
            simp_rw [mul_assoc]
            rw [avg_mul_left, avg_mul_left]
      · exact le_rfl
    _ = _ := by
      have heq (a : α) :
          (if group a then |fixed a| * (M * u a * avg (fun b => v b * core b)) else 0) =
            M * (if group a then |fixed a| * u a else 0) * avg (fun b => v b * core b) := by
        split_ifs <;> ring
      simp_rw [heq]
      rw [avg_mul_right, avg_mul_left]
      ring

lemma avg_equiv [Fintype α] [Fintype β] (e : α ≃ β) (f : α → ℝ) :
    avg f = avg (fun b => f (e.symm b)) := by
  rw [avg, avg, Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (by intro a; simp)

end OrdinaryCorrelations.FiniteIntegration

end

end OAI
