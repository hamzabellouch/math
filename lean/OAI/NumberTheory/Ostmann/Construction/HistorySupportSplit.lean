import OAI.NumberTheory.Ostmann.Construction.Coefficient

namespace OAI

noncomputable section
open scoped ComplexConjugate Classical
namespace Ostmann.Construction.History

def giantGuard (a : State) {l : ℕ} (h : History l) : Prop :=
  ∀ v∈h.frequencies, Nat.Coprime a.giantPlus v.natAbs ∧ Nat.Coprime a.giantMinus v.natAbs

def rootConditions (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ) (a : State) : Prop :=
  a.Positive ∧ a.PrimeSmall ∧ a.TemplateAt l ∧ a.Coprime outside ∧
    a.frequency≠0 ∧ a.frequency.natAbs≤V l

def nodeRelations (l : ℕ) (a : State) (p : ℕ) (u hp hm : List SmallSlot)
    (b c : State) : Prop :=
  0<p ∧ (∀ q∈u, q.role=.compensation l) ∧ a.small.Perm (hp++hm) ∧
    b.giantPlus=p ∧ c.giantPlus=p ∧ b.giantMinus=a.giantPlus ∧ c.giantMinus=a.giantMinus ∧
    b.small.Perm (u++hp) ∧ c.small.Perm (u++hm) ∧
    Arithmetic.reversalNumerator b.frequency c.frequency
      ((a.giantPlus*(hp.map SmallSlot.value).prod:ℕ):ℤ)
      ((a.giantMinus*(hm.map SmallSlot.value).prod:ℕ):ℤ) =
        a.frequency*((u.map SmallSlot.value).prod:ℤ)*(p:ℤ)

theorem giantGuard_node (a b : State) (p : ℕ) (u hp hm : List SmallSlot)
    {l : ℕ} (left right : History l) :
    giantGuard a (History.node b p u hp hm left right) ↔
      (Nat.Coprime a.giantPlus b.frequency.natAbs ∧
        Nat.Coprime a.giantMinus b.frequency.natAbs) ∧
      giantGuard a left ∧ giantGuard a right := by
  constructor
  · intro h
    refine ⟨h b.frequency (by simp [frequencies]), ?_, ?_⟩
    · intro v hv
      exact h v (by simp [frequencies, hv])
    · intro v hv
      exact h v (by simp [frequencies, hv])
  · rintro ⟨h0,hl,hr⟩ v hv
    simp only [frequencies, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv | hv
    · exact h0
    · exact hl v hv
    · exact hr v hv

theorem supported_node_iff (V : ℕ → ℕ) (outside : List ℕ)
    (a : State) (p : ℕ) (u hp hm : List SmallSlot) {l : ℕ} (left right : History l) :
    (History.node a p u hp hm left right).Supported V outside ↔
      (rootConditions V outside (l+1) a ∧
        (Nat.Coprime a.giantPlus a.frequency.natAbs ∧
          Nat.Coprime a.giantMinus a.frequency.natAbs) ∧
        nodeRelations (l+1) a p u hp hm left.root right.root) ∧
      (left.Supported V outside ∧ giantGuard a left) ∧
      (right.Supported V outside ∧ giantGuard a right) := by
  have hguard : (History.node a p u hp hm left right).GiantUnits ↔
      (Nat.Coprime a.giantPlus a.frequency.natAbs ∧
        Nat.Coprime a.giantMinus a.frequency.natAbs) ∧
      giantGuard a left ∧ giantGuard a right := giantGuard_node a a p u hp hm left right
  rw [Supported, hguard]
  simp only [root, rootConditions, nodeRelations]
  tauto

def guardedWeight (a : State) (V : ℕ → ℕ) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ) {l : ℕ} (h : History l) : ℂ := by
  classical
  exact if h.Supported V outside ∧ giantGuard a h then h.weight base φ G else 0

theorem supportedWeight_node (V : ℕ → ℕ) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    (a : State) (p : ℕ) (u hp hm : List SmallSlot) {l : ℕ} (left right : History l) :
    (History.node a p u hp hm left right).supportedWeight V outside base φ G =
      if rootConditions V outside (l+1) a ∧
        (Nat.Coprime a.giantPlus a.frequency.natAbs ∧
          Nat.Coprime a.giantMinus a.frequency.natAbs) ∧
        nodeRelations (l+1) a p u hp hm left.root right.root then
          (((u.map SmallSlot.value).prod:ℂ)*(φ (Real.log p-G):ℂ))*
            guardedWeight a V outside base φ G left *
              conj (guardedWeight a V outside base φ G right)
        else 0 := by
  classical
  unfold supportedWeight
  rw [supported_node_iff]
  by_cases hlocal : rootConditions V outside (l+1) a ∧
    (Nat.Coprime a.giantPlus a.frequency.natAbs ∧
      Nat.Coprime a.giantMinus a.frequency.natAbs) ∧
    nodeRelations (l+1) a p u hp hm left.root right.root <;>
    by_cases hl : left.Supported V outside ∧ giantGuard a left <;>
    by_cases hr : right.Supported V outside ∧ giantGuard a right <;>
    simp only [hlocal, hl, hr, and_true, and_false, true_and,
      ite_true, ite_false, ite_self, guardedWeight, weight, map_zero, mul_zero, zero_mul]

end Ostmann.Construction.History

end

end OAI
