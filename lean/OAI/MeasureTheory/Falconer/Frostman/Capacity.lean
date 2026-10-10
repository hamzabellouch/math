import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFalconer

inductive CapacityTree where
  | leaf (cap : ℝ)
  | node (cap : ℝ) (t₀ t₁ t₂ t₃ : CapacityTree)

def CapacityTree.rootCapacity : CapacityTree → ℝ
  | .leaf c => c
  | .node c _ _ _ _ => c

def CapacityTree.nonnegative : CapacityTree → Prop
  | .leaf c => 0 ≤ c
  | .node c t₀ t₁ t₂ t₃ =>
      0 ≤ c ∧ t₀.nonnegative ∧ t₁.nonnegative ∧ t₂.nonnegative ∧ t₃.nonnegative

noncomputable def CapacityTree.effective : CapacityTree → ℝ
  | .leaf c => c
  | .node c t₀ t₁ t₂ t₃ => min c (t₀.effective+t₁.effective+t₂.effective+t₃.effective)

inductive CutCost : CapacityTree → ℝ → Prop where
  | root (t : CapacityTree) : CutCost t t.rootCapacity
  | children {c t₀ t₁ t₂ t₃ z₀ z₁ z₂ z₃}
      (h₀ : CutCost t₀ z₀) (h₁ : CutCost t₁ z₁)
      (h₂ : CutCost t₂ z₂) (h₃ : CutCost t₃ z₃) :
      CutCost (.node c t₀ t₁ t₂ t₃) (z₀+z₁+z₂+z₃)

theorem effective_le_root (t : CapacityTree) : t.effective ≤ t.rootCapacity := by
  cases t with
  | leaf c => exact le_rfl
  | node c t₀ t₁ t₂ t₃ => exact min_le_left _ _

theorem effective_le_cut {t : CapacityTree} {z : ℝ} (h : CutCost t z) :
    t.effective ≤ z := by
  induction h with
  | root t => exact effective_le_root t
  | children h₀ h₁ h₂ h₃ ih₀ ih₁ ih₂ ih₃ =>
    exact (min_le_right _ _).trans (by linarith)

theorem effective_cut (t : CapacityTree) : CutCost t t.effective := by
  induction t with
  | leaf c => exact CutCost.root (.leaf c)
  | node c t₀ t₁ t₂ t₃ ih₀ ih₁ ih₂ ih₃ =>
    change CutCost (.node c t₀ t₁ t₂ t₃)
      (min c (t₀.effective+t₁.effective+t₂.effective+t₃.effective))
    by_cases h : c ≤ t₀.effective+t₁.effective+t₂.effective+t₃.effective
    · rw [min_eq_left h]
      exact CutCost.root (.node c t₀ t₁ t₂ t₃)
    · rw [min_eq_right (le_of_not_ge h)]
      exact CutCost.children ih₀ ih₁ ih₂ ih₃

theorem effective_is_minimum_cut (t : CapacityTree) :
    CutCost t t.effective ∧ ∀ z, CutCost t z → t.effective ≤ z :=
  ⟨effective_cut t,fun _ h => effective_le_cut h⟩

theorem effective_nonnegative {t : CapacityTree} (h : t.nonnegative) :
    0 ≤ t.effective := by
  induction t with
  | leaf c => exact h
  | node c t₀ t₁ t₂ t₃ ih₀ ih₁ ih₂ ih₃ =>
    obtain ⟨hc,h₀,h₁,h₂,h₃⟩ := h
    exact le_min hc (by linarith [ih₀ h₀,ih₁ h₁,ih₂ h₂,ih₃ h₃])

theorem split_four {c₀ c₁ c₂ c₃ m : ℝ}
    (h₀ : 0 ≤ c₀) (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃)
    (hm : 0 ≤ m) (htotal : m ≤ c₀+c₁+c₂+c₃) :
    ∃ m₀ m₁ m₂ m₃ : ℝ,
      (0 ≤ m₀ ∧ m₀ ≤ c₀) ∧ (0 ≤ m₁ ∧ m₁ ≤ c₁) ∧
      (0 ≤ m₂ ∧ m₂ ≤ c₂) ∧ (0 ≤ m₃ ∧ m₃ ≤ c₃) ∧
      m₀+m₁+m₂+m₃ = m := by
  let s := c₀+c₁+c₂+c₃
  by_cases hs : s = 0
  · have hm0 : m = 0 := by dsimp [s] at hs; linarith
    exact ⟨0,0,0,0,⟨le_rfl,h₀⟩,⟨le_rfl,h₁⟩,⟨le_rfl,h₂⟩,⟨le_rfl,h₃⟩,by simp [hm0]⟩
  · have hspos : 0 < s := by dsimp [s] at *; positivity
    have hb (c : ℝ) (hc : 0 ≤ c) : 0 ≤ m*c/s ∧ m*c/s ≤ c := by
      constructor
      · positivity
      · apply (div_le_iff₀ hspos).mpr
        dsimp [s]
        nlinarith
    refine ⟨m*c₀/s,m*c₁/s,m*c₂/s,m*c₃/s,hb _ h₀,hb _ h₁,hb _ h₂,hb _ h₃,?_⟩
    field_simp
    dsimp [s]

inductive Routes : CapacityTree → ℝ → Prop where
  | leaf {c m} (hm : 0 ≤ m) (hc : m ≤ c) : Routes (.leaf c) m
  | node {c t₀ t₁ t₂ t₃ m m₀ m₁ m₂ m₃}
      (hm : 0 ≤ m) (hc : m ≤ c) (hsum : m₀+m₁+m₂+m₃=m)
      (h₀ : Routes t₀ m₀) (h₁ : Routes t₁ m₁)
      (h₂ : Routes t₂ m₂) (h₃ : Routes t₃ m₃) :
      Routes (.node c t₀ t₁ t₂ t₃) m

theorem routes_of_le_effective (t : CapacityTree) (hn : t.nonnegative)
    (m : ℝ) (hm : 0 ≤ m) (hcap : m ≤ t.effective) : Routes t m := by
  induction t generalizing m with
  | leaf c => exact Routes.leaf hm hcap
  | node c t₀ t₁ t₂ t₃ ih₀ ih₁ ih₂ ih₃ =>
    obtain ⟨hc,hn₀,hn₁,hn₂,hn₃⟩ := hn
    obtain ⟨hmcap,hmsum⟩ := le_min_iff.mp hcap
    obtain ⟨m₀,m₁,m₂,m₃,⟨hp₀,hu₀⟩,⟨hp₁,hu₁⟩,⟨hp₂,hu₂⟩,⟨hp₃,hu₃⟩,hs⟩ :=
      split_four (effective_nonnegative hn₀) (effective_nonnegative hn₁)
        (effective_nonnegative hn₂) (effective_nonnegative hn₃) hm hmsum
    exact Routes.node hm hmcap hs (ih₀ hn₀ m₀ hp₀ hu₀) (ih₁ hn₁ m₁ hp₁ hu₁)
      (ih₂ hn₂ m₂ hp₂ hu₂) (ih₃ hn₃ m₃ hp₃ hu₃)

theorem routes_of_cut_lower_bound (t : CapacityTree) (hn : t.nonnegative)
    (m : ℝ) (hm : 0 ≤ m) (hcuts : ∀ z, CutCost t z → m ≤ z) : Routes t m :=
  routes_of_le_effective t hn m hm (hcuts _ (effective_cut t))

end PlanarFalconer

end OAI
