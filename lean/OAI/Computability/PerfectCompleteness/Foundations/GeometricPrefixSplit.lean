import Lean.Elab.Tactic.Omega
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas

namespace OAI

section

namespace PerfectCompleteness.GeometricPrefixSplit

open RecursiveSpaces DescendantSpaces
open GeometricCutSplit (Prefix PrefixDepth prefixPathDepth prefixPath castPath prefixLaw)
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

variable {branch : Nat → Nat}

def depthEquiv (low b : Nat) : (a : Nat) →
    PrefixDepth branch low (b + a) ≃
      PrefixDepth branch (low + b) a × PrefixDepth branch low b
  | 0 =>
      { toFun := fun x => ((), x)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨⟨⟩, x⟩; rfl }
  | a + 1 =>
      ((Equiv.cast (congrArg (fun h => Fin (branch h))
        (Nat.add_assoc low b a).symm)).prodCongr (depthEquiv low b a)).trans
          (Equiv.prodAssoc _ _ _).symm

private theorem castPath_step {x y low : Nat} (h : x = y)
    (c : Fin (branch x)) (p : Path branch x low) :
    castPath (congrArg Nat.succ h) (.step c p) =
      .step (Equiv.cast (congrArg (fun n => Fin (branch n)) h) c)
        (castPath h p) := by
  cases h
  rfl

theorem depthEquiv_path (low b a : Nat)
    (x : PrefixDepth branch low (b + a)) :
    castPath (Nat.add_assoc low b a).symm (prefixPathDepth low (b + a) x) =
      (prefixPathDepth (low + b) a (depthEquiv low b a x).1).append
        (prefixPathDepth low b (depthEquiv low b a x).2) := by
  revert x
  induction a with
  | zero => intro x; rfl
  | succ a ih =>
      intro x
      change castPath (congrArg Nat.succ (Nat.add_assoc low b a).symm)
        (.step x.1 (prefixPathDepth low (b + a) x.2)) = _
      rw [castPath_step (Nat.add_assoc low b a).symm x.1
        (prefixPathDepth low (b + a) x.2)]
      exact congrArg (Path.step _) (ih x.2)

private theorem castPath_trans {x y z low : Nat} (h : x = y) (g : y = z)
    (p : Path branch x low) :
    castPath g (castPath h p) = castPath (h.trans g) p := by
  cases h
  cases g
  rfl

private theorem prefixPathDepth_cast {low d e : Nat} (h : d = e)
    (x : PrefixDepth branch low d) :
    prefixPathDepth low e (Equiv.cast (congrArg (PrefixDepth branch low) h) x) =
      castPath (congrArg (fun n => low + n) h) (prefixPathDepth low d x) := by
  cases h
  rfl

private theorem castPath_append {x y mid low : Nat} (h : x = y)
    (p : Path branch x mid) (q : Path branch mid low) :
    castPath h (p.append q) = (castPath h p).append q := by
  cases h
  rfl

private theorem castPath_depth_append {x y low : Nat} (h : x = y) (a : Nat)
    (upper : PrefixDepth branch x a) (lower : Path branch x low) :
    castPath (congrArg (fun n => n + a) h)
        ((prefixPathDepth x a upper).append lower) =
      (prefixPathDepth y a
        (Equiv.cast (congrArg (fun n => PrefixDepth branch n a) h) upper)).append
          (castPath h lower) := by
  cases h
  rfl

variable {root mid low : Nat}

def splitEquiv (hlow : low ≤ mid) (hmid : mid ≤ root) :
    Prefix branch root low ≃ Prefix branch root mid × Prefix branch mid low :=
  (Equiv.cast (congrArg (PrefixDepth branch low)
    (show root - low = (mid - low) + (root - mid) by omega))).trans
      ((depthEquiv low (mid - low) (root - mid)).trans
        ((Equiv.cast (congrArg (fun n => PrefixDepth branch n (root - mid))
          (Nat.add_sub_of_le hlow))).prodCongr (Equiv.refl _)))

def joinEquiv (hlow : low ≤ mid) (hmid : mid ≤ root) :
    Prefix branch root mid × Prefix branch mid low ≃ Prefix branch root low :=
  (splitEquiv hlow hmid).symm

@[simp] theorem split_join (hlow : low ≤ mid) (hmid : mid ≤ root)
    (pair : Prefix branch root mid × Prefix branch mid low) :
    splitEquiv hlow hmid (joinEquiv hlow hmid pair) = pair :=
  (splitEquiv hlow hmid).apply_symm_apply pair

@[simp] theorem join_split (hlow : low ≤ mid) (hmid : mid ≤ root)
    (pref : Prefix branch root low) :
    joinEquiv hlow hmid (splitEquiv hlow hmid pref) = pref :=
  (splitEquiv hlow hmid).symm_apply_apply pref

theorem prefixPath_split (hlow : low ≤ mid) (hmid : mid ≤ root)
    (pref : Prefix branch root low) :
    prefixPath (hlow.trans hmid) pref =
      (prefixPath hmid (splitEquiv hlow hmid pref).1).append
        (prefixPath hlow (splitEquiv hlow hmid pref).2) := by
  let a := root - mid
  let b := mid - low
  have hd : root - low = b + a := by dsimp [a, b]; omega
  have hm : low + b = mid := Nat.add_sub_of_le hlow
  let x : PrefixDepth branch low (b + a) :=
    Equiv.cast (congrArg (PrefixDepth branch low) hd) pref
  calc
    prefixPath (hlow.trans hmid) pref =
        castPath (Nat.add_sub_of_le hmid)
          (castPath (congrArg (fun n => n + a) hm)
            (castPath (Nat.add_assoc low b a).symm
              (prefixPathDepth low (b + a) x))) := by
      dsimp only [x]
      rw [prefixPathDepth_cast hd pref]
      simp only [castPath_trans]
      rfl
    _ = castPath (Nat.add_sub_of_le hmid)
        (castPath (congrArg (fun n => n + a) hm)
          ((prefixPathDepth (low + b) a (depthEquiv low b a x).1).append
            (prefixPathDepth low b (depthEquiv low b a x).2))) := by
      rw [depthEquiv_path]
    _ = castPath (Nat.add_sub_of_le hmid)
        ((prefixPathDepth mid a
          (Equiv.cast (congrArg (fun n => PrefixDepth branch n a) hm)
            (depthEquiv low b a x).1)).append
          (castPath hm (prefixPathDepth low b (depthEquiv low b a x).2))) := by
      rw [castPath_depth_append]
    _ = (prefixPath hmid (splitEquiv hlow hmid pref).1).append
        (prefixPath hlow (splitEquiv hlow hmid pref).2) := by
      rw [castPath_append]
      rfl

theorem prefixPath_split_spec (hlow : low ≤ mid) (hmid : mid ≤ root)
    (pref : Prefix branch root low) :
    (⟨low, prefixPath (hlow.trans hmid) pref⟩ : Σ height, Path branch root height) =
      ⟨low, (prefixPath hmid (splitEquiv hlow hmid pref).1).append
        (prefixPath hlow (splitEquiv hlow hmid pref).2)⟩ :=
  congrArg (fun p : Path branch root low =>
    (⟨low, p⟩ : Σ height, Path branch root height)) (prefixPath_split hlow hmid pref)

theorem prefixPath_join (hlow : low ≤ mid) (hmid : mid ≤ root)
    (upper : Prefix branch root mid) (lower : Prefix branch mid low) :
    prefixPath (hlow.trans hmid) (joinEquiv hlow hmid (upper, lower)) =
      (prefixPath hmid upper).append (prefixPath hlow lower) := by
  simpa only [split_join] using
    prefixPath_split hlow hmid (joinEquiv hlow hmid (upper, lower))

noncomputable section

theorem law_split (hlow : low ≤ mid) (hmid : mid ≤ root)
    (hbranch : ∀ k < root, 0 < branch k) :
    (prefixLaw (hlow.trans hmid) hbranch).pushforward (splitEquiv hlow hmid) =
      (prefixLaw hmid hbranch).product
        (prefixLaw hlow (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hmid))) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro pair
  change (1 : ℝ) / (Fintype.card (Prefix branch root low) : ℝ) =
    ((1 : ℝ) / (Fintype.card (Prefix branch root mid) : ℝ)) *
      ((1 : ℝ) / (Fintype.card (Prefix branch mid low) : ℝ))
  rw [Fintype.card_congr (splitEquiv (branch := branch) hlow hmid),
    Fintype.card_prod, Nat.cast_mul]
  simp only [one_div_mul_one_div]

theorem expectation_split (hlow : low ≤ mid) (hmid : mid ≤ root)
    (hbranch : ∀ k < root, 0 < branch k)
    (f : Prefix branch root mid → Prefix branch mid low → ℝ) :
    (prefixLaw (hlow.trans hmid) hbranch).expectation
        (fun pref => f (splitEquiv hlow hmid pref).1 (splitEquiv hlow hmid pref).2) =
      (prefixLaw hmid hbranch).expectation (fun upper =>
        (prefixLaw hlow (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hmid))).expectation
          (f upper)) := by
  rw [← FiniteDistribution.expectation_pushforward
    (prefixLaw (hlow.trans hmid) hbranch) (splitEquiv hlow hmid)
    (fun pair => f pair.1 pair.2), law_split, FiniteDistribution.expectation_product]

end
end PerfectCompleteness.GeometricPrefixSplit

end

end OAI
