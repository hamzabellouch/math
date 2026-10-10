import Mathlib

namespace OAI

universe u v

noncomputable section

namespace Problem313
namespace Reindex

variable {ι : Type u} {κ : Type v}

def config (e : ι ≃ κ) (x : ι → Bool) : κ → Bool := fun j => x (e.symm j)

def configEquiv (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) where
  toFun := config e
  invFun := config e.symm
  left_inv x := by ext i; simp [config]
  right_inv x := by ext i; simp [config]

@[simp] theorem config_apply (e : ι ≃ κ) (x : ι → Bool) (i : ι) :
    config e x (e i) = x i := by simp [config]

@[simp] theorem configEquiv_apply (e : ι ≃ κ) (x : ι → Bool) :
    configEquiv e x = config e x := rfl

theorem config_update [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (x : ι → Bool) (i : ι) (b : Bool) :
    config e (Function.update x i b) = Function.update (config e x) (e i) b := by
  classical
  ext j
  by_cases h : j = e i
  · subst j; simp [config]
  · have h' : e.symm j ≠ i := by
      intro he
      apply h
      simpa using congrArg e he
    simp [config, h, h']

def weight [Fintype ι] (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i = true then p else 1 - p

def influence [Fintype ι] (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ := by
  classical
  exact ∑ x, if f (Function.update x i true) ≠ f (Function.update x i false)
    then weight p x else 0

theorem weight_config [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (p : ℝ) (x : ι → Bool) : weight p (config e x) = weight p x := by
  unfold weight
  exact (Fintype.prod_equiv e _ _ (fun i => by simp)).symm

theorem influence_config [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (p : ℝ) (f : (ι → Bool) → Bool) (g : (κ → Bool) → Bool)
    (hfg : ∀ x, g (config e x) = f x) (i : ι) :
    influence p g (e i) = influence p f i := by
  classical
  unfold influence
  apply Eq.symm
  apply Fintype.sum_equiv (configEquiv e)
  intro x
  simp only [configEquiv_apply, ← config_update, hfg, weight_config]

theorem weight_nonneg [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ι → Bool) : 0 ≤ weight p x := by
  unfold weight
  apply Finset.prod_nonneg
  intro i hi
  split_ifs <;> linarith

theorem influence_nonneg [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) (i : ι) : 0 ≤ influence p f i := by
  classical
  unfold influence
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact weight_nonneg hp0 hp1 x
  · exact le_rfl

/-- An orbit of at least `m` equally influential coordinates bounds each influence. -/
theorem influence_le_total_div [Fintype ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → Bool) (i : ι)
    (S : Finset ι) {m : ℝ} (hm : 0 < m) (hcard : m ≤ (S.card : ℝ))
    (heq : ∀ j ∈ S, influence p f j = influence p f i) :
    influence p f i ≤ (∑ j, influence p f j) / m := by
  classical
  have hi := influence_nonneg hp0 hp1 f i
  have hS : (S.card : ℝ) * influence p f i = ∑ j ∈ S, influence p f j := by
    calc
      (S.card : ℝ) * influence p f i = ∑ _j ∈ S, influence p f i := by simp
      _ = ∑ j ∈ S, influence p f j := Finset.sum_congr rfl (fun j hj => (heq j hj).symm)
  have hsum : (∑ j ∈ S, influence p f j) ≤ ∑ j, influence p f j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro j hj hjS
    exact influence_nonneg hp0 hp1 f j
  apply (le_div_iff₀ hm).2
  calc
    influence p f i * m = m * influence p f i := mul_comm _ _
    _ ≤ (S.card : ℝ) * influence p f i := mul_le_mul_of_nonneg_right hcard hi
    _ = ∑ j ∈ S, influence p f j := hS
    _ ≤ ∑ j, influence p f j := hsum

end Reindex
end Problem313

end

end OAI
