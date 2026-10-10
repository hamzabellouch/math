import OAI.Probability.DilutedSpin.MarkerHistory

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance markerHistoryTransportDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω C D ι : Type} [Fintype Ω] [DecidableEq C] [DecidableEq D] [DecidableEq ι] {n : ℕ}

omit [Fintype Ω] in
/-- Enlarging the color set by protected old paths does not change any
extension choice or its coefficient. -/
theorem labeledHistory_reindex (m : Fin (n+1) → ℝ) (e : C → D) (he : Function.Injective e)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : D → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => V R (pos ∘ e) g) (cs.map e) S U loc pos f =
      labeledHistory m V cs S U loc (pos ∘ e) f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons,labeledHistory,ih,Function.update_comp_eq_of_injective _ he]
    rfl

/-- In a splitting ultrametric, a path separating from a marker before every
old path has the same split from each of those old paths. -/
lemma splitDepth_eq_of_lt (S : PrescribedTree n) (a b c : S.Leaf)
    (h : splitDepth S a b < splitDepth S b c) :
    splitDepth S a c = splitDepth S a b := by
  have h₁ := splitDepth_ultrametric S a b c
  have h₂ := splitDepth_ultrametric S a c b
  rw [splitDepth_symm S c b] at h₂
  omega

variable [Fintype C] [Fintype D]

omit [DecidableEq C] [DecidableEq D] [Fintype C] [Fintype D] in
/-- A matrix on the new colors and a single marker determines all their
splits from the protected old tree when the old tree has not yet branched at
the prescribed separation depth. -/
theorem marker_matrix_iff (S Q : PrescribedTree n)
    (old : D → S.Leaf) (fresh : C → S.Leaf) (a : D)
    (qold : D → Q.Leaf) (qfresh : C → Q.Leaf)
    (hold : ∀ d e, splitDepth S (old d) (old e)=splitDepth Q (qold d) (qold e))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a)<splitDepth Q (qold a) (qold d)) :
    (∀ x y : Option C,
      splitDepth S (Option.elim' (old a) fresh x) (Option.elim' (old a) fresh y)=
      splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y)) ↔
    (∀ x y : D ⊕ C,
      splitDepth S (Sum.elim old fresh x) (Sum.elim old fresh y)=
      splitDepth Q (Sum.elim qold qfresh x) (Sum.elim qold qfresh y)) := by
  constructor
  · intro h x y
    have hcross (c : C) (d : D) : splitDepth S (fresh c) (old d)=splitDepth Q (qfresh c) (qold d) := by
      have hm := h (some c) none
      change splitDepth S (fresh c) (old a)=splitDepth Q (qfresh c) (qold a) at hm
      have hs : splitDepth S (fresh c) (old a)<splitDepth S (old a) (old d) := by
        rw [hm,hold]; exact hsep c d
      rw [splitDepth_eq_of_lt S _ _ _ hs,hm,splitDepth_eq_of_lt Q _ _ _ (hsep c d)]
    cases x with
    | inl d =>
      cases y with
      | inl e => exact hold d e
      | inr c => simpa only [Sum.elim_inl,Sum.elim_inr,splitDepth_symm] using hcross c d
    | inr c =>
      cases y with
      | inl d => exact hcross c d
      | inr b => exact h (some c) (some b)
  · intro h x y
    have hh := h (Option.elim' (Sum.inl a) Sum.inr x) (Option.elim' (Sum.inl a) Sum.inr y)
    cases x <;> cases y <;> exact hh

end DilutedSpinGlass.PrescribedTree

end

end OAI
