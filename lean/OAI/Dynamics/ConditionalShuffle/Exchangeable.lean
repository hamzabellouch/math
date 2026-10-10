import OAI.Dynamics.ConditionalShuffle.SweepAverage

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional

lemma mean_perm_eval {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (a : α) :
    mean (fun g : Equiv.Perm α => f (g a)) = mean f := by
  let : Nonempty α := ⟨a⟩
  have he (b : α) : mean (fun g : Equiv.Perm α => f (g b)) =
      mean (fun g : Equiv.Perm α => f (g a)) := by
    have hh := mean_equiv (Equiv.mulRight (Equiv.swap a b)) (fun g : Equiv.Perm α => f (g a))
    change mean (fun g : Equiv.Perm α => f ((g * Equiv.swap a b) a)) = _ at hh
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using hh
  calc
    _ = mean (fun b : α => mean (fun g : Equiv.Perm α => f (g b))) := by
      simp only [he, mean_const]
    _ = mean (fun g : Equiv.Perm α => mean (fun b : α => f (g b))) := mean_comm _
    _ = mean (fun _ : Equiv.Perm α => mean f) :=
      mean_congr (fun g => mean_equiv g f)
    _ = _ := mean_const _

lemma mean_perm_cross_nonpos {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ)
    (hw : ∑ a, w a = 0) (a b : α) (hab : a ≠ b) :
    mean (fun g : Equiv.Perm α => w (g a) * w (g b)) ≤ 0 := by
  let C := mean (fun g : Equiv.Perm α => w (g a) * w (g b))
  have hc (x : α) (hx : x ≠ a) :
      mean (fun g : Equiv.Perm α => w (g a) * w (g x)) = C := by
    have hh := mean_equiv (Equiv.mulRight (Equiv.swap b x))
      (fun g : Equiv.Perm α => w (g a) * w (g b))
    change mean (fun g : Equiv.Perm α => w ((g * Equiv.swap b x) a) *
      w ((g * Equiv.swap b x) b)) = _ at hh
    simpa only [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hab hx.symm, Equiv.swap_apply_left] using hh
  have hz : mean (fun g : Equiv.Perm α => ∑ x, w (g a) * w (g x)) = 0 := by
    have hh (g : Equiv.Perm α) : (∑ x, w (g a) * w (g x)) = 0 := by
      rw [← Finset.mul_sum, Equiv.sum_comp g w, hw, mul_zero]
    simp only [hh, mean_zero]
  rw [mean_sum, Fintype.sum_eq_add_sum_subtype_ne _ a] at hz
  have hs : (∑ x : {x : α // x ≠ a}, mean (fun g : Equiv.Perm α => w (g a) * w (g x.val))) =
      Fintype.card {x : α // x ≠ a} * C := by
    calc
      _ = ∑ _ : {x : α // x ≠ a}, C := Finset.sum_congr rfl (fun x _ => hc x.val x.property)
      _ = _ := by simp
  rw [hs] at hz
  have hnonneg := mean_nonneg (fun g : Equiv.Perm α => mul_self_nonneg (w (g a)))
  have hcard : (0 : ℝ) < Fintype.card {x : α // x ≠ a} := by
    have hh : 0 < Fintype.card {x : α // x ≠ a} :=
      Fintype.card_pos_iff.mpr ⟨⟨b,hab.symm⟩⟩
    exact_mod_cast hh
  change C ≤ 0
  nlinarith

lemma mean_permuted_matrix_energy_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [Nonempty α] (w : α → ℝ) (hw : ∑ a, w a = 0) (K : α → β → ℝ)
    (hK : ∀ a y, 0 ≤ K a y) :
    mean (fun σ : Equiv.Perm α => ∑ y, (∑ a, w (σ a) * K a y)^2) ≤
      mean (fun a => w a ^ 2) * ∑ a, ∑ y, K a y ^ 2 := by
  have hterm (a b : α) (y : β) :
      mean (fun σ : Equiv.Perm α => (w (σ a) * K a y) * (w (σ b) * K b y)) ≤
      if b = a then mean (fun x => w x ^ 2) * K a y ^ 2 else 0 := by
    by_cases h : b = a
    · subst b
      have hh (σ : Equiv.Perm α) : (w (σ a) * K a y) * (w (σ a) * K a y) =
          (w (σ a))^2 * (K a y)^2 := by ring
      rw [ite_eq_left rfl]
      simp only [hh, mean_mul_const]
      rw [mean_perm_eval (fun x => w x ^ 2) a]
    · rw [ite_eq_right h]
      have hh (σ : Equiv.Perm α) : (w (σ a) * K a y) * (w (σ b) * K b y) =
          (w (σ a) * w (σ b)) * (K a y * K b y) := by ring
      simp only [hh, mean_mul_const]
      exact mul_nonpos_of_nonpos_of_nonneg (mean_perm_cross_nonpos w hw a b (fun ha => h ha.symm))
        (mul_nonneg (hK a y) (hK b y))
  calc
    _ = ∑ y, ∑ a, ∑ b,
        mean (fun σ : Equiv.Perm α => (w (σ a) * K a y) * (w (σ b) * K b y)) := by
      simp only [sq, Finset.sum_mul, Finset.mul_sum, mean_sum]
      apply Finset.sum_congr rfl; intro y _
      exact Finset.sum_comm
    _ ≤ ∑ y, ∑ a, ∑ b,
        if b = a then mean (fun x => w x ^ 2) * K a y ^ 2 else 0 :=
      Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun a _ =>
        Finset.sum_le_sum (fun b _ => hterm a b y)))
    _ = _ := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]

end Thorp.Conditional

end

end OAI
