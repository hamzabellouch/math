import OAI.Probability.FreeIsing.Trees.BroadcastLocality
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

noncomputable section

namespace Problem367
namespace RootedBroadcast

def branchRoot {d : ℕ} (c : Fin d) : TreeVertex d :=
  ⟨[c], List.IsChain.singleton c⟩

@[simp] theorem branchRoot_val {d : ℕ} (c : Fin d) : (branchRoot c).val = [c] := rfl

@[simp] theorem prefixFlip_root {d : ℕ} (c : Fin d) :
    prefixFlip c (root d) = branchRoot c := rfl

@[simp] theorem prefixFlip_branchRoot {d : ℕ} (c : Fin d) :
    prefixFlip c (branchRoot c) = root d := by
  apply Subtype.ext
  simp [prefixFlip, prefixFlipWord, branchRoot, root]

theorem not_prefix_flip_of_prefix {d : ℕ} (c : Fin d) (v : TreeVertex d)
    (hv : [c] <+: v.val) : ¬ [c] <+: (prefixFlip c v).val := by
  rcases v with ⟨w, hw⟩
  rcases hv with ⟨t, ht⟩
  have heq : w = c :: t := by simpa using ht.symm
  subst w
  simp only [prefixFlip, prefixFlipWord]
  cases t with
  | nil => simp
  | cons b t =>
    have hcb : c ≠ b := (List.isChain_cons_cons.mp hw).1
    intro hprefix
    have heq : [c] = [b] :=
      (List.prefix_of_prefix_length_le hprefix (by simp) (by simp)).eq_of_length (by simp)
    exact hcb (by simpa using heq)

theorem prefix_flip_iff_not_prefix {d : ℕ} (c : Fin d) (v : TreeVertex d) :
    [c] <+: (prefixFlip c v).val ↔ ¬ [c] <+: v.val := by
  constructor
  · intro h
    simpa only [prefixFlip_twice] using
      not_prefix_flip_of_prefix c (prefixFlip c v) h
  · intro h
    rcases v with ⟨w, hw⟩
    cases w with
    | nil => simp [prefixFlip, prefixFlipWord]
    | cons b t =>
      have hcb : c ≠ b := by
        intro heq
        subst b
        exact h (by simp)
      simp [prefixFlip, prefixFlipWord, hcb]

def flipBranchToComplement {d : ℕ} (c : Fin d) (v : BranchVertex c) :
    {w : TreeVertex d // ¬ [c] <+: w.val} :=
  ⟨prefixFlip c v.val, not_prefix_flip_of_prefix c v.val v.property⟩

@[simp] theorem flipBranchToComplement_val {d : ℕ} (c : Fin d) (v : BranchVertex c) :
    (flipBranchToComplement c v).val = prefixFlip c v.val := rfl

def flipBranchEquivComplement {d : ℕ} (c : Fin d) :
    BranchVertex c ≃ {w : TreeVertex d // ¬ [c] <+: w.val} where
  toFun := flipBranchToComplement c
  invFun := fun w => ⟨prefixFlip c w.val, (prefix_flip_iff_not_prefix c w.val).mpr w.property⟩
  left_inv := fun v => Subtype.ext (prefixFlip_twice c v.val)
  right_inv := fun w => Subtype.ext (prefixFlip_twice c w.val)

def branchRootVertex {d : ℕ} (c : Fin d) : BranchVertex c :=
  ⟨branchRoot c, List.prefix_refl [c]⟩

@[simp] theorem prefixTreeAut_symm_root {d : ℕ} (c : Fin d) :
    (prefixTreeAut c).toEquiv.symm (root d) = branchRoot c := rfl

@[simp] theorem prefixTreeAut_symm_branchRoot {d : ℕ} (c : Fin d) :
    (prefixTreeAut c).toEquiv.symm (branchRoot c) = root d :=
  prefixFlip_branchRoot c

theorem treeAdj_root_branchRoot {d : ℕ} (c : Fin d) :
    treeAdj (root d) (branchRoot c) := Or.inl ⟨c, rfl⟩

end RootedBroadcast
end Problem367

end

end OAI
