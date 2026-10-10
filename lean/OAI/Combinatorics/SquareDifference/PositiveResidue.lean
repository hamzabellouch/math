import OAI.Combinatorics.SquareDifference.LowProduct

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma exists_strict_square_steps (p : ℕ) [Fact p.Prime] :
    ∃ δ : ℕ → ZMod p, (∀j, δ j≠0 ∧ IsSquare (δ j)) ∧ ∑j∈range 24, δ j=0 := by
  classical
  by_cases hs : IsSquare (-1 : ZMod p)
  · let δ : ℕ → ZMod p := fun j => if j%2=0 then 1 else -1
    refine ⟨δ,?_,?_⟩
    · intro j
      dsimp [δ]
      split_ifs
      · exact ⟨one_ne_zero, ⟨1, by simp⟩⟩
      · exact ⟨neg_ne_zero.mpr one_ne_zero,hs⟩
    · norm_num [δ,Finset.sum_range_succ]
  · obtain ⟨a,b,hab⟩ := ZMod.sq_add_sq p (-1)
    have ha : a^2≠0 := by
      intro h
      have he : -1=b*b := by simpa [h,pow_two] using hab.symm
      exact hs ⟨b,he⟩
    have hb : b^2≠0 := by
      intro h
      have he : -1=a*a := by simpa [h,pow_two] using hab.symm
      exact hs ⟨a,he⟩
    let δ : ℕ → ZMod p := fun j => if j%3=0 then a^2 else if j%3=1 then b^2 else 1
    refine ⟨δ,?_,?_⟩
    · intro j
      dsimp [δ]
      split_ifs
      · exact ⟨ha,⟨a,by rw [pow_two]⟩⟩
      · exact ⟨hb,⟨b,by rw [pow_two]⟩⟩
      · exact ⟨one_ne_zero,⟨1,by simp⟩⟩
    · norm_num only [δ,Finset.sum_range_succ,Finset.sum_range_zero,
        Nat.reduceMod,Nat.reduceEqDiff,ite_true,ite_false,zero_add]
      linear_combination 8*hab

lemma prefix_cyclic_difference {G : Type*} [AddCommGroup G]
    (δ : ℕ → G) (hδ : ∑j∈range 24, δ j=0) (j : Fin 24) :
    (∑k∈range (j+1).val, δ k)-(∑k∈range j.val, δ k)=δ j.val := by
  by_cases hj : j.val<23
  · have hval : (j+1).val=j.val+1 := by
      rw [Fin.val_add]
      norm_num only [Fin.val_one]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hval,sum_range_succ,add_sub_cancel_left]
  · have hj23 : j.val=23 := by omega
    have hval : (j+1).val=0 := by rw [Fin.val_add,hj23]; norm_num
    rw [hval,hj23,sum_range_zero,zero_sub]
    have hh := hδ
    rw [show 24=23+1 by rfl,sum_range_succ] at hh
    simpa using congrArg Neg.neg (eq_neg_iff_add_eq_zero.mpr hh)

lemma exists_cyclic_labels {G V : Type*} [AddCommGroup G]
    (ι : Fin 24 → V) (hι : Function.Injective ι) (δ : ℕ → G)
    (hδ : ∑j∈range 24, δ j=0) :
    ∃ s : V → G, ∀j : Fin 24, s (ι (j+1))-s (ι j)=δ j.val := by
  classical
  let f : Fin 24 → G := fun j => ∑k∈range j.val, δ k
  let s : V → G := Function.extend ι f (fun _ => 0)
  refine ⟨s,?_⟩
  intro j
  dsimp [s]
  rw [Function.Injective.extend_apply hι,Function.Injective.extend_apply hι]
  exact prefix_cyclic_difference δ hδ j

lemma exists_product_strict_steps {I : Type*} (p : I → ℕ) [∀i, Fact (p i).Prime]
    {D : ℕ} (e : ZMod D ≃+* (ZMod 8 × ∀i, ZMod (p i))) :
    ∃ δ : ℕ → ZMod D, (∀j, (e (δ j)).1=1 ∧
      ∀i, (e (δ j)).2 i≠0 ∧ IsSquare ((e (δ j)).2 i)) ∧
      (∑j∈range 24, δ j)=0 := by
  classical
  choose d hd hd0 using fun i => exists_strict_square_steps (p i)
  let δ : ℕ → ZMod D := fun j => e.symm (1,fun i => d i j)
  refine ⟨δ,?_,?_⟩
  · intro j
    simp only [δ,e.apply_symm_apply]
    exact ⟨trivial,fun i => hd i j⟩
  · apply e.injective
    rw [map_sum,map_zero]
    simp only [δ,e.apply_symm_apply]
    ext
    · simp only [Prod.fst_sum]
      norm_num only [sum_const,card_range,nsmul_eq_mul,mul_one]
      change (24 : ZMod 8)=0
      decide
    · simp only [Prod.snd_sum,Finset.sum_apply,Prod.snd_zero,Pi.zero_apply]
      exact hd0 _

lemma exists_good_cyclic_labels {I V : Type*} (p : I → ℕ) [∀i, Fact (p i).Prime]
    {D : ℕ} (e : ZMod D ≃+* (ZMod 8 × ∀i, ZMod (p i)))
    (ι : Fin 24 → V) (hι : Function.Injective ι) :
    ∃ s : V → ZMod D, ∀j : Fin 24,
      (e (s (ι (j+1))-s (ι j))).1=1 ∧
      ∀i, (e (s (ι (j+1))-s (ι j))).2 i≠0 ∧
        IsSquare ((e (s (ι (j+1))-s (ι j))).2 i) := by
  obtain ⟨δ,hδ,hδ0⟩ := exists_product_strict_steps p e
  obtain ⟨s,hs⟩ := exists_cyclic_labels ι hι δ hδ0
  exact ⟨s,fun j => by rw [hs j]; exact hδ j.val⟩

end SquareDifference

namespace SquareDifference

lemma tupleCycle_order : orderOf tupleCycle=24 := by
  change orderOf (finRotate 24)=24
  rw [(isCycle_finRotate_of_le (show 2≤24 by decide)).orderOf,
    support_finRotate_of_le (show 2≤24 by decide)]
  simp

lemma cycleVertex_fin_injective : Function.Injective (fun j : Fin 24 => cycleVertex j.val) := by
  intro i j hij
  apply Fin.ext
  have he := congrFun hij (⟨0,by decide⟩ : Fin tupleBlocks)
  change tupleCycle^i.val=tupleCycle^j.val at he
  exact pow_injOn_Iio_orderOf (by simp [tupleCycle_order])
    (by simp [tupleCycle_order]) he

lemma cycleVertex_fin_successor (j : Fin 24) :
    cycleVertex (j+1).val=cycleVertex (j.val+1) := by
  by_cases hj : j.val<23
  · congr 1
    rw [Fin.val_add]
    norm_num only [Fin.val_one]
    exact Nat.mod_eq_of_lt (by omega)
  · have hj23 : j.val=23 := by omega
    have hv : (j+1).val=0 := by rw [Fin.val_add,hj23]; norm_num
    rw [hv,hj23]
    exact (cycleVertex_period 0).symm

lemma exists_good_tuple_residues {I : Type*} (p : I → ℕ) [∀i,Fact (p i).Prime]
    {D : ℕ} (e : ZMod D ≃+* (ZMod 8 × ∀i,ZMod (p i))) :
    ∃s : TupleVertex → ZMod D,∀j : Fin 24,
      (e (s (cycleVertex (j.val+1))-s (cycleVertex j.val))).1=1 ∧
      ∀i,(e (s (cycleVertex (j.val+1))-s (cycleVertex j.val))).2 i≠0 ∧
      IsSquare ((e (s (cycleVertex (j.val+1))-s (cycleVertex j.val))).2 i) := by
  obtain ⟨s,hs⟩ := exists_good_cyclic_labels p e _ cycleVertex_fin_injective
  refine ⟨s,fun j => ?_⟩
  simpa only [cycleVertex_fin_successor] using hs j

lemma uniform_event_positive {X : Type*} [Fintype X] [Nonempty X]
    (P : X → Prop) [DecidablePred P] (hP : ∃x,P x) :
    0<(𝔼 x,if P x then (1:ℝ) else 0) := by
  obtain ⟨x,hx⟩ := hP
  rw [expect_eq_sum_div_card]
  apply div_pos _ (by exact_mod_cast Fintype.card_pos)
  apply sum_pos' (fun _ _ => by positivity)
  exact ⟨x,mem_univ x,by rw [ite_eq_left hx]; norm_num⟩

end SquareDifference

end

end OAI
