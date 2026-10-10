import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyModelPaths

namespace OAI

/-! # Fixed factors and ancestor coefficients of the frequency model -/

namespace Ostmann
open scoped Classical

def FrequencyModelState.leftProduct {σ : Type*} (value : σ → ℕ) : FrequencyModelState σ → ℤ
  | ⟨0, _, _, _⟩ => 1
  | ⟨_ + 1, .node _ CL _ _ _ _, x, _⟩ => x * (MovingSlotReversal.naturalProduct value CL : ℤ)

def FrequencyModelState.rightProduct {σ : Type*} (value : σ → ℕ) : FrequencyModelState σ → ℤ
  | ⟨0, _, _, _⟩ => 1
  | ⟨_ + 1, .node _ _ CR _ _ _, _, y⟩ => y * (MovingSlotReversal.naturalProduct value CR : ℤ)

def FrequencyModelState.compensation {σ : Type*} (value : σ → ℕ) : FrequencyModelState σ → ℤ
  | ⟨0, _, _, _⟩ => 1
  | ⟨_ + 1, .node _ _ _ U _ _, _, _⟩ => MovingSlotReversal.naturalProduct value U

def frequencyModelPivots {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (T : MovingSlotData σ n) (x y : ℤ) (j : Fin (2 ^ n - 1)) : ℤ :=
  (frequencyModelAtPath value R n T x y (preorderNodePath n j)).pivot value R

theorem frequencyModelAtPath_giants {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (T : MovingSlotData σ n) (x y : ℤ) (path : List Bool) (hp : path.length < n)
    (d : ℕ) (p : ℕ → ℤ)
    (hanc : ∀ k < path.length, p (d + k) =
      (frequencyModelAtPath value R n T x y (path.take k)).pivot value R) :
    let z := frequencyModelAtPath value R n T x y path
    (z.leftGiant, z.rightGiant) = evolveGiantValues p d (x, y) path := by
  induction n generalizing x y path d with
  | zero => simp at hp
  | succ n ih =>
    cases T with
    | node s CL CR U l r =>
      cases path with
      | nil => rfl
      | cons b path =>
        have hp' : path.length < n := by simpa using hp
        let q := (MovingSlotData.step s CL CR U l r false).frequencyPivot value R (n + 1) x y
        have hq : p d = q := by
          simpa only [Nat.add_zero, List.take_zero, frequencyModelAtPath,
            FrequencyModelState.pivot] using hanc 0 (by simp)
        cases b <;> simp only [frequencyModelAtPath, Bool.false_eq_true, ite_false, ite_true]
        · rw [evolveGiantValues, hq]
          apply ih l q x path hp' (d + 1)
          intro k hk
          have h := hanc (k + 1) (by simpa using Nat.add_lt_add_right hk 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1 k, List.take_succ_cons,
            frequencyModelAtPath, Bool.false_eq_true, ite_false] using h
        · rw [evolveGiantValues, hq]
          apply ih r q y path hp' (d + 1)
          intro k hk
          have h := hanc (k + 1) (by simpa using Nat.add_lt_add_right hk 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1 k, List.take_succ_cons,
            frequencyModelAtPath, ite_true] using h

theorem frequencyModelPivots_sources {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (T : MovingSlotData σ n) (x y : ℤ) (j : Fin (2 ^ n - 1)) :
    let p := frequencyModelPivots value R n T x y
    let z := frequencyModelAtPath value R n T x y (preorderNodePath n j)
    (z.leftGiant, z.rightGiant) =
      ((historyGiantSources x y (preorderNodePath n j)).1.nodeValue n j p
        (historyGiantSources_known x y _).1,
       (historyGiantSources x y (preorderNodePath n j)).2.nodeValue n j p
        (historyGiantSources_known x y _).2) := by
  dsimp only
  let p := frequencyModelPivots value R n T x y
  let q := fun k => if hk : k < (preorderNodePath n j).length then
    p (ancestorNodeIndex n j ⟨k, hk⟩) else 0
  have h := frequencyModelAtPath_giants value R n T x y (preorderNodePath n j)
    (preorderNodePath_length n j) 0 q (by
      intro k hk
      simp only [Nat.zero_add, q, dite_eq_left hk, p, frequencyModelPivots, ancestorNodeIndex_path])
  have heval := evolveGiantSources_eval q 0 (.fixed x, .fixed y) (preorderNodePath n j)
  change _ = evolveGiantValues q 0 (x, y) (preorderNodePath n j) at heval
  rw [← heval] at h
  change _ = ((historyGiantSources x y (preorderNodePath n j)).1.eval q,
    (historyGiantSources x y (preorderNodePath n j)).2.eval q) at h
  rw [h]
  have he (s : HistoryGiantSource) (hs : s.knownBefore (preorderNodePath n j).length) :
      s.eval q = s.nodeValue n j p hs := by
    cases s with
    | fixed c => rfl
    | ancestor i =>
      change (if hi : i < (preorderNodePath n j).length then
        p (ancestorNodeIndex n j ⟨i, hi⟩) else 0) = _
      change i < (preorderNodePath n j).length at hs
      rw [dite_eq_left hs]
      rfl
  exact Prod.ext (he _ (historyGiantSources_known x y _).1)
    (he _ (historyGiantSources_known x y _).2)

theorem frequencyModelAtPath_products {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (x y : ℤ) (path : List Bool) (hp : path.length < n) :
    let z := frequencyModelAtPath value R n (buildMovingSlotData n t small bulk a) x y path
    let c := movingFrameConstants value n small a path
    let b := movingBulkProducts value n bulk path
    z.compensation value = c.compensation ∧
      z.leftProduct value = z.leftGiant * c.leftSmall * b.1 ∧
      z.rightProduct value = z.rightGiant * c.rightSmall * b.2 := by
  induction n generalizing x y path with
  | zero => simp at hp
  | succ n ih =>
    cases a with
    | node a l r =>
      cases path with
      | nil =>
        simp only [frequencyModelAtPath, buildMovingSlotData, movingFrameConstants,
          movingBulkProducts, FrequencyModelState.compensation, FrequencyModelState.leftProduct,
          FrequencyModelState.rightProduct, movingNaturalProduct_append, Nat.cast_mul,
          mul_assoc, and_self]
      | cons b path =>
        have hp' : path.length < n := by simpa using hp
        cases b
        · exact ih t.2.1 (appendMovingSlotLeaves n (movingCompensationSlots n a) small.1)
            bulk.1 l _ x path hp'
        · exact ih t.2.2 (appendMovingSlotLeaves n (movingCompensationSlots n a) small.2)
            bulk.2 r _ y path hp'

noncomputable def frequencyModelAncestorScheme {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ) :
    PivotDependencyScheme (2 ^ n - 1) :=
  forwardTreeAncestorScheme S n t x y
    (fun path => (movingFrameConstants value n small a path).leftSmall)
    (fun path => (movingFrameConstants value n small a path).rightSmall)

theorem frequencyModelNode_products {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n)
    (x y : ℤ) (j : Fin (2 ^ n - 1)) :
    let tz := frequencyTreeMap Subtype.val n t
    let T := buildMovingSlotData n tz small bulk a
    let p := frequencyModelPivots value R n T x y
    let D := frequencyModelAncestorScheme value S n t small a x y
    let z := frequencyModelAtPath value R n T x y (preorderNodePath n j)
    let b := (actualChildProducts n (treeLeafMap (fun q : ℕ => (q : ℤ)) n
      (movingSlotValues value n bulk))).getD j.val (1, 1)
    z.compensation value = movingSampleCompensation value n small a j ∧
      z.leftProduct value = D.rightCoefficient p j * b.1 ∧
      z.rightProduct value = D.leftCoefficient p j * b.2 := by
  dsimp only
  have hf := frequencyModelAtPath_products value R n (frequencyTreeMap Subtype.val n t)
    small bulk a x y (preorderNodePath n j) (preorderNodePath_length n j)
  have hg := frequencyModelPivots_sources value R n
    (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a) x y j
  have hb := movingBulkProducts_preorder_intCast value n bulk j
  have hl := congrArg Prod.fst hg
  have hr := congrArg Prod.snd hg
  have hbl := congrArg Prod.fst hb
  have hbr := congrArg Prod.snd hb
  dsimp only at hl hr hbl hbr
  refine ⟨hf.1, ?_, ?_⟩
  · rw [hf.2.1]
    change _ = (forwardTreeAncestorScheme S n t x y _ _).rightCoefficient _ j * _
    rw [forwardTreeAncestorScheme_right, ← hl, ← hbl]
    ring
  · rw [hf.2.2]
    change _ = (forwardTreeAncestorScheme S n t x y _ _).leftCoefficient _ j * _
    rw [forwardTreeAncestorScheme_left, ← hr, ← hbr]
    ring

end Ostmann

end OAI
