import OAI.Probability.DilutedSpin.ScheduledTopology
import OAI.Probability.DilutedSpin.ShiftedTree
import OAI.Probability.DilutedSpin.StemTwoSideProjection

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

lemma stemLeaf_bijective (S : PrescribedTree n) (r : ℕ) :
    Function.Bijective (stemLeaf S r) := by
  induction r with
  | zero => exact Function.bijective_id
  | succ r ih =>
    constructor
    · intro a b h
      apply ih.1
      exact (Sigma.mk.inj h).2.eq
    · rintro ⟨i,b⟩
      have hi := Fin.eq_zero i
      subst i
      obtain ⟨a,rfl⟩ := ih.2 b
      exact ⟨a,rfl⟩

/-- The actual projector uses only the sampled stem. It does not depend on
which old descendant leaf represents that stem. -/
lemma tailMean_path_stem (S : PrescribedTree n) (r : ℕ) (a b : S.Leaf)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ)
    (z : Sample Ω (stem S r)) :
    tailMean S r T f ((stem S r).pathAt (stemLeaf S r a) z) =
      tailMean S r T f ((stem S r).pathAt (stemLeaf S r b) z) := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih (T.2 (z 0).1) (fun y => f ((z 0).1,y)) (z 0).2

lemma tailMean_any_path_stem (S : PrescribedTree n) (r : ℕ) (a b : (stem S r).Leaf)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ)
    (z : Sample Ω (stem S r)) :
    tailMean S r T f ((stem S r).pathAt a z) =
      tailMean S r T f ((stem S r).pathAt b z) := by
  obtain ⟨a,rfl⟩ := (stemLeaf_bijective S r).2 a
  obtain ⟨b,rfl⟩ := (stemLeaf_bijective S r).2 b
  exact tailMean_path_stem S r a b T f z

/-- In the literal two-copy old tree, every leaf opposite the anchor has
exactly the same projected vector as the designated old-II leaf. This is
the geometric hOld premise of the full signed-matrix estimate. -/
theorem doubled_stem_projector_old_side (S : PrescribedTree n) (r : ℕ)
    (a b : (stem S r).Leaf) (T : KernelTower Ω (n+r+1))
    (f : FinitePath Ω (n+r+1) → Fin N → ℝ)
    (c : (doubled (stem S r)).Leaf)
    (hc : splitDepth (doubled (stem S r)) ⟨0,a⟩ c=0)
    (z : Sample Ω (doubled (stem S r))) :
    (fun i => tailMean S (r+1) T (fun x => f x i)
      ((doubled (stem S r)).pathAt c z)) =
    (fun i => tailMean S (r+1) T (fun x => f x i)
      ((doubled (stem S r)).pathAt ⟨1,b⟩ z)) := by
  rcases c with ⟨j,c⟩
  have hj : j ≠ 0 := by
    intro h
    subst j
    change splitDepth (.node 2 (fun _ => stem S r)) ⟨0,a⟩ ⟨0,c⟩=0 at hc
    rw [splitDepth_same_child] at hc
    omega
  have hj1 : j=1 := by
    apply Fin.ext
    have hh := j.isLt
    have hn : j.val ≠ 0 := fun h => hj (Fin.ext h)
    change j.val=1
    norm_num at hh
    omega
  subst j
  funext i
  exact tailMean_any_path_stem S r c b (T.2 (z 1).1) (fun y => f ((z 1).1,y) i) (z 1).2

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

lemma leaf_card_pos (S : ReducedTopology) : 0<Fintype.card S.Leaf := by
  induction S with
  | leaf => exact Nat.zero_lt_one
  | node k hk C ih =>
    change 0<Fintype.card ((j : Fin k) × (C j).Leaf)
    rw [Fintype.card_sigma]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨⟨0,k.property⟩,Finset.mem_univ _,ih _⟩

/-- Every proper child consumes strictly fewer leaves, without suppressing
or identifying distinct child occurrences with the same topology. -/
lemma child_leaf_card_lt (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (j : Fin k) : Fintype.card (C j).Leaf <
      Fintype.card (ReducedTopology.node k hk C).Leaf := by
  classical
  have hi : ∃ i : Fin k, i≠j := by
    by_cases hj : j=⟨0,k.property⟩
    · refine ⟨⟨1,by omega⟩,?_⟩
      intro h
      have hh := congrArg Fin.val (h.trans hj)
      change (1:ℕ)=0 at hh
      omega
    · exact ⟨⟨0,k.property⟩,Ne.symm hj⟩
  obtain ⟨i,hij⟩ := hi
  change _ < Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma,← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  apply Nat.lt_add_of_pos_right
  exact (leaf_card_pos (C i)).trans_le
    (Finset.single_le_sum (f := fun x : Fin k => Fintype.card (C x).Leaf) (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hij,Finset.mem_univ i⟩))

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
