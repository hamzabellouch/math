import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

/-- `lem:density`, including the convention of closing a nonflat argument. -/
def DensityExpansionContract (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) : Prop :=
  Monotone (densityExpansion M hE κ D) ∧
  ∀ P : Set α,
    IsDensityMax M κ D P (densityExpansion M hE κ D P) ∧
    (∀ Q, IsDensityMax M κ D P Q → Q ⊆ densityExpansion M hE κ D P) ∧
    P ⊆ densityExpansion M hE κ D P ∧
    densityExpansion M hE κ D (M.closure P) = densityExpansion M hE κ D P ∧
    ∀ Z : Set α,
      (D ∩ (M.closure (densityExpansion M hE κ D P ∪ Z) \
        densityExpansion M hE κ D P)).ncard ≤
        κ * conditionalRank M Z (densityExpansion M hE κ D P)

/-- `lem:paths`: both paths, all integer endpoints, and the true least birth. -/
def PathPropertiesContract (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) : Prop :=
  ∀ h : ℕ,
    Monotone (nominalPath M hE κ D C h) ∧
    Monotone (guardedPath M hE κ D C (h + 1)) ∧
    (∀ k : ℤ,
      guardedPath M hE κ D C h k ⊆ nominalPath M hE κ D C h k ∧
      nominalPath M hE κ D C h k ⊆ guardedPath M hE κ D C (h + 1) k ∧
      guardedPath M hE κ D C (h + 1) k ⊆ nominalPath M hE κ D C h (k + 1)) ∧
    (∀ k : ℤ, 0 ≤ k →
      nominalPath M hE κ D C h k = univ ∧
      guardedPath M hE κ D C (h + 1) k = univ) ∧
    (∀ k : ℤ, k < activation h → nominalPath M hE κ D C h k = M.closure ∅) ∧
    (∀ k : ℤ, k < activation h - 1 →
      guardedPath M hE κ D C (h + 1) k = M.closure ∅) ∧
    ∀ e : α, e ∉ M.closure ∅ →
      IsLeast {k : ℤ | e ∈ nominalPath M hE κ D C h k}
        (nominalBirth M hE κ D C h e) ∧
      ((nominalBirth M hE κ D C h e = activation h ∧
        e ∈ densityExpansion M hE κ (D h) (M.closure ∅)) ∨
       (activation h + 2 ≤ nominalBirth M hE κ D C h e ∧
        nominalBirth M hE κ D C h e ≤ 0))

/-- `lem:generators`: one budget and one increasing family for the entire ℤ path. -/
def GeneratorBudgetContract (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) : Prop :=
  ∀ h : ℕ,
    (∃ G : Set α, G ⊆ D h ∧ κ * G.ncard ≤ (D h).ncard ∧
      ∃ J : ℤ → Set α, Monotone J ∧ (∀ k, J k ⊆ G) ∧
        ∀ k : ℤ, nominalPath M hE κ D C h k =
          M.closure (guardedPath M hE κ D C h k ∪ J k)) ∧
    κ * natRank M (densityExpansion M hE κ (D h) (M.closure ∅)) ≤ (D h).ncard

end MatroidProphet

end OAI
