import OAI.NumberTheory.Ostmann.Characters.TreeTupleProfiles

namespace OAI

/-! # A horizontal cut preserves the original sibling conjugations -/

namespace Ostmann

theorem rationalQuartetStates_conjugations {p : ℕ} [Fact p.Prime]
    (n : ℕ) {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ (n + 2) C)
    (XL XR : (ZMod p)ˣ) (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafTuple (ZMod p)ˣ n)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c P = some S) :
    treeLeafMap RationalQuartetState.conjugations n S = quartetBlockTupleEquiv Bool n c := by
  induction n generalizing C XL XR with
  | zero =>
    have h := Option.some.inj hS
    cases h
    rfl
  | succ n ih =>
    cases T with
    | node s CL CR u left right =>
      simp only [rationalQuartetStates] at hS
      split_ifs at hS with hv
      let V : (ZMod p)ˣ := Units.mk0
          (reconstructedEntry (s : ZMod p) left.frequency right.frequency u
            (XL * CL * treeLeafProduct n P.1) (XR * CR * treeLeafProduct n P.2)) hv
      change (do
        let L ← rationalQuartetStates n left V XL c.1 P.1
        let R ← rationalQuartetStates n right V XR c.2 P.2
        pure (L, R)) = some S at hS
      cases hL : rationalQuartetStates n left V XL c.1 P.1 with
      | none => simp [hL] at hS
      | some L =>
        cases hR : rationalQuartetStates n right V XR c.2 P.2 with
        | none => simp [hL, hR] at hS
        | some R =>
          have he : (L, R) = S := by simpa [hL, hR] using hS
          subst S
          exact Prod.ext (ih left V XL c.1 P.1 L hL) (ih right V XR c.2 P.2 R hR)

theorem rationalQuartetStates_conjugations_at {p : ℕ} [Fact p.Prime]
    (n : ℕ) {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ (n + 2) C)
    (XL XR : (ZMod p)ˣ) (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafTuple (ZMod p)ˣ n)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c P = some S) (i : TreeLeafIndex n) :
    (treeLeafTupleEquiv _ n S i).conjugations = quartetBlockEquiv Bool n c i := by
  have h := congrArg (fun s => treeLeafTupleEquiv _ n s i)
    (rationalQuartetStates_conjugations n T XL XR c P S hS)
  simpa only [treeLeafTupleEquiv_map, quartetBlockEquiv, Equiv.trans_apply] using h

end Ostmann

end OAI
