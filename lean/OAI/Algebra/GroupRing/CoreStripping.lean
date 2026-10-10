import Mathlib
import OAI.Algebra.GroupRing.DegreeTwoSuppression

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.CoreStripping
open PortSubdivision
open scoped Classical
variable {V D : Type*} (Γ : PortGraph V D)

def degree (S : Finset D) (v : V) : ℕ := (S.filter (fun d => Γ.origin d=v)).card

def Symmetric (S : Finset D) : Prop := ∀ d ∈ S, Γ.reverse d ∈ S

def delete (S : Finset D) (d : D) : Finset D := (S.erase d).erase (Γ.reverse d)

lemma delete_subset (S : Finset D) (d : D) : delete Γ S d ⊆ S :=
  (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)

lemma degree_pos (S : Finset D) {d : D} (hd : d∈S) : 0 < degree Γ S (Γ.origin d) := by
  exact Finset.card_pos.mpr ⟨d,Finset.mem_filter.mpr ⟨hd,rfl⟩⟩

lemma leaf_unique (S : Finset D) {d : D} (hd : d∈S) (hleaf : degree Γ S (Γ.origin d)=1)
    {e : D} (he : e∈S) (ho : Γ.origin e=Γ.origin d) : e=d := by
  have hu := Finset.card_eq_one.mp hleaf
  obtain ⟨z,hz⟩ := hu
  have hd' : d∈S.filter (fun e => Γ.origin e=Γ.origin d) := by simp [hd]
  have he' : e∈S.filter (fun e => Γ.origin e=Γ.origin d) := by simp [he,ho]
  rw [hz] at hd' he'
  exact (Finset.mem_singleton.mp he').trans (Finset.mem_singleton.mp hd').symm

lemma leaf_not_loop (S : Finset D) (hs : Symmetric Γ S) {d : D} (hd : d∈S)
    (hleaf : degree Γ S (Γ.origin d)=1) : Γ.origin (Γ.reverse d)≠Γ.origin d := by
  intro he
  exact Γ.reverse_ne d (leaf_unique Γ S hd hleaf (hs d hd) he)

lemma delete_symmetric (S : Finset D) (hs : Symmetric Γ S) (d : D) :
    Symmetric Γ (delete Γ S d) := by
  intro e he
  simp only [delete,Finset.mem_erase] at he ⊢
  refine ⟨?_,?_,hs e he.2.2⟩
  · exact fun h => he.2.1 (Γ.reverse_reverse.injective h)
  · intro h
    have hh := congrArg Γ.reverse h
    rw [Γ.reverse_reverse] at hh
    exact he.1 hh

lemma delete_degree_leaf (S : Finset D) {d : D} (hd : d∈S)
    (hleaf : degree Γ S (Γ.origin d)=1) : degree Γ (delete Γ S d) (Γ.origin d)=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,ho⟩ := Finset.mem_filter.mp he
  have heq := leaf_unique Γ S hd hleaf (delete_subset Γ S d he) ho
  exact (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1 heq

lemma delete_degree_neighbor (S : Finset D) (hs : Symmetric Γ S) {d : D} (hd : d∈S)
    (hleaf : degree Γ S (Γ.origin d)=1) :
    degree Γ (delete Γ S d) (Γ.origin (Γ.reverse d))+1 = degree Γ S (Γ.origin (Γ.reverse d)) := by
  have hn := leaf_not_loop Γ S hs hd hleaf
  have he : (delete Γ S d).filter (fun e => Γ.origin e=Γ.origin (Γ.reverse d)) =
      (S.filter (fun e => Γ.origin e=Γ.origin (Γ.reverse d))).erase (Γ.reverse d) := by
    ext e
    simp only [delete,Finset.mem_filter,Finset.mem_erase]
    constructor
    · tauto
    · rintro ⟨he,hs',ho⟩
      refine ⟨⟨he,?_,hs'⟩,ho⟩
      intro hd'
      subst e
      exact hn ho.symm
  unfold degree
  rw [he]
  exact Finset.card_erase_add_one (by simp [hs d hd])

lemma delete_degree_other (S : Finset D) (d : D) {v : V}
    (hu : v≠Γ.origin d) (hv : v≠Γ.origin (Γ.reverse d)) :
    degree Γ (delete Γ S d) v=degree Γ S v := by
  unfold degree
  congr 1
  ext e
  simp only [delete,Finset.mem_filter,Finset.mem_erase]
  constructor
  · tauto
  · rintro ⟨he,ho⟩
    refine ⟨⟨?_,?_,he⟩,ho⟩
    · intro hh; subst e; exact hv ho.symm
    · intro hh; subst e; exact hu ho.symm

/-- Euler surplus without counting isolated vertices. It equals the sum of
branch excesses minus the number of leaves. -/
def surplus (n : ℕ) : ℤ := if n=0 then 0 else (n:ℤ)-2

lemma surplus_succ (n : ℕ) : surplus (n+1) ≤ surplus n+1 := by
  rcases n with _ | n
  · norm_num [surplus]
  · simp only [surplus,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.cast_add,Nat.cast_one]
    omega

variable [Fintype V]

def potential (S : Finset D) : ℤ := ∑ v, surplus (degree Γ S v)

lemma delete_potential (S : Finset D) (hs : Symmetric Γ S) {d : D} (hd : d∈S)
    (hleaf : degree Γ S (Γ.origin d)=1) : potential Γ S≤potential Γ (delete Γ S d) := by
  have hn := leaf_not_loop Γ S hs hd hleaf
  have hpoint (v : V) : surplus (degree Γ S v) ≤
      surplus (degree Γ (delete Γ S d) v) + (if v=Γ.origin (Γ.reverse d) then 1 else 0) -
        (if v=Γ.origin d then 1 else 0) := by
    by_cases hu : v=Γ.origin d
    · subst v
      rw [hleaf,delete_degree_leaf Γ S hd hleaf]
      simp [surplus,Ne.symm hn]
    · by_cases hv : v=Γ.origin (Γ.reverse d)
      · subst v
        rw [← delete_degree_neighbor Γ S hs hd hleaf]
        simpa only [ite_eq_left rfl,ite_eq_right hn,ite_true,sub_zero] using surplus_succ
          (degree Γ (delete Γ S d) (Γ.origin (Γ.reverse d)))
      · rw [delete_degree_other Γ S d hu hv,ite_eq_right hu,ite_eq_right hv,add_zero,sub_zero]
  have hsum := Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hpoint v)
  unfold potential
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,add_sub_cancel_right] using hsum

/-- Actual repeated leaf deletion. The terminal subgraph has minimum degree
two on every surviving dart; Euler surplus can only increase. -/
theorem exists_core (S : Finset D) (hs : Symmetric Γ S) :
    ∃ Q : Finset D, Q⊆S ∧ Symmetric Γ Q ∧
      (∀ d∈Q, 2≤degree Γ Q (Γ.origin d)) ∧ potential Γ S≤potential Γ Q := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hleaf : ∃ d∈S, degree Γ S (Γ.origin d)=1
    · obtain ⟨d,hd,hleaf⟩ := hleaf
      let S' := delete Γ S d
      have hlt : S'.card<n := by
        have he : S'.card≤(S.erase d).card := Finset.card_le_card (Finset.erase_subset _ _)
        have ht := Finset.card_erase_lt_of_mem hd
        omega
      obtain ⟨Q,hQS,hQ,hdeg,hpot⟩ := ih S'.card hlt S' (delete_symmetric Γ S hs d) rfl
      exact ⟨Q,hQS.trans (delete_subset Γ S d),hQ,hdeg,
        (delete_potential Γ S hs hd hleaf).trans hpot⟩
    · refine ⟨S,Finset.Subset.refl _,hs,?_,le_refl _⟩
      intro d hd
      have hp := degree_pos Γ S hd
      have hn : degree Γ S (Γ.origin d)≠1 := by aesop
      omega

end TorsionFreeZeroDivisors.CoreStripping

namespace TorsionFreeZeroDivisors.ImageComplexity
open PortSubdivision WeightedPortMoore WeightedCycles CoreStripping
open scoped BigOperators Classical
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)

/-- The actual symmetric subgraph on a specified set of original darts. -/
def restrict (Q : Finset D) (hs : Symmetric Γ Q) : PortGraph V Q where
  origin d := Γ.origin d
  reverse d := ⟨Γ.reverse d,hs d d.property⟩
  reverse_reverse d := Subtype.ext (Γ.reverse_reverse d)
  reverse_ne d h := Γ.reverse_ne d (congrArg Subtype.val h)

def inclusion (Q : Finset D) (hs : Symmetric Γ Q) :
    (restrict Γ Q hs).subdivision →g Γ.subdivision where
  toFun := Sum.map id Subtype.val
  map_rel' := by
    intro a b h
    rcases a with a|a <;> rcases b with b|b
    · exact h
    · exact h
    · exact h
    · exact congrArg Subtype.val h

omit [Fintype V] [Fintype D] in
lemma inclusion_injective (Q : Finset D) (hs : Symmetric Γ Q) :
    Function.Injective (inclusion Γ Q hs) := Sum.map_injective.mpr ⟨Function.injective_id,Subtype.val_injective⟩

omit [Fintype V] [Fintype D] in
lemma restrict_degree (Q : Finset D) (hs : Symmetric Γ Q) (v : V) :
    (DegreeTwoSuppression.out (restrict Γ Q hs).origin v).card=degree Γ Q v := by
  classical
  unfold DegreeTwoSuppression.out degree
  apply Finset.card_bij (fun d _ => d.val)
  · intro d hd
    exact Finset.mem_filter.mpr ⟨d.property,(Finset.mem_filter.mp hd).2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro d hd
    refine ⟨⟨d,(Finset.mem_filter.mp hd).1⟩,?_,rfl⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (Finset.mem_filter.mp hd).2

omit [Fintype V] [Fintype D] in
lemma inclusion_weight (Q : Finset D) (hs : Symmetric Γ Q) {a b : V ⊕ Q}
    (p : (restrict Γ Q hs).subdivision.Walk a b) :
    weight (edgeWeight (fun _ : D => (1:ℝ))) (p.map (inclusion Γ Q hs)) =
      weight (edgeWeight (fun _ : Q => (1:ℝ))) p := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.map_cons,weight_cons,weight_cons,ih]
    congr 1
    cases a <;> cases b <;> rfl

omit [Fintype D] in
/-- Vertexwise counting, including loops through their two different darts. -/
lemma fiber_count (S : Finset D) (P : V → Prop) [DecidablePred P] :
    ∑ v, (if P v then degree Γ S v else 0) = (S.filter (fun d => P (Γ.origin d))).card := by
  classical
  unfold degree
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  trans ∑ v, ∑ d ∈ S, if Γ.origin d=v ∧ P v then 1 else 0
  · apply Finset.sum_congr rfl
    intro v hv
    by_cases hh : P v <;> simp [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp [ite_and]

lemma surplus_excess (n : ℕ) : surplus n = ((n-2:ℕ):ℤ) - (if n=1 then 1 else 0) := by
  unfold surplus
  split_ifs <;> omega

lemma surplus_le_branch (n : ℕ) : surplus n ≤ (if n=2 then (0:ℕ) else n) := by
  unfold surplus
  split_ifs <;> omega

omit [Fintype D] in
lemma excess_le_potential_add_leaves (S : Finset D) :
    ((∑ v, (degree Γ S v - 2) : ℕ):ℤ) ≤ potential Γ S +
      ((Finset.univ.filter (fun v => degree Γ S v=1)).card:ℤ) := by
  unfold potential
  simp only [surplus_excess,Finset.sum_sub_distrib,Nat.cast_sum]
  have he : (∑ v : V, (if degree Γ S v=1 then (1:ℤ) else 0)) =
      ((Finset.univ.filter (fun v => degree Γ S v=1)).card:ℤ) := by simp
  rw [he]
  omega

omit [Fintype D] in
lemma branch_degrees_bound_excess (S : Finset D) :
    (S.filter (fun d => 3 ≤ degree Γ S (Γ.origin d))).card ≤
      3 * (∑ v, (degree Γ S v - 2)) := by
  rw [← fiber_count Γ S (fun v => 3 ≤ degree Γ S v),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  split_ifs <;> omega

/-- Bounded branching in the actual image, not in a hypothesized bounded-rank
pattern. A bounded number of leaves is the only endpoint correction. -/
theorem bounded_image_branches (C : ℝ) (hC : 0 ≤ C) (leaves : ℕ) :
    ∃ R : ℕ, ∀ {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)
      (L : ℝ) (_ : 0 < L)
      (_ : (Fintype.card D:ℝ) ≤ 2*C*L)
      (_ : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
        L ≤ weight (edgeWeight (fun _ : D => (1:ℝ))) c)
      (_ : (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card ≤ leaves),
      (Finset.univ.filter (fun d => 3≤degree Γ Finset.univ (Γ.origin d))).card ≤ R := by
  obtain ⟨R,hR⟩ := SuppressedMoore.bounded_branch_ports C hC
  refine ⟨3*(R+leaves),?_⟩
  intro V D _ _ Γ L hL htot hg hl
  obtain ⟨Q,_hQ,hs,hmin,hpot⟩ := exists_core Γ Finset.univ (by simp [CoreStripping.Symmetric])
  have hsub : (Fintype.card Q:ℝ)≤2*C*L := by
    exact (Nat.cast_le.mpr (by simpa using Finset.card_le_univ Q)).trans htot
  have hbound := hR (restrict Γ Q hs) (fun d => by
    rw [restrict_degree]; exact hmin d d.property) L hL hsub (by
      intro a c hc
      have hp := hg _ (c.map (inclusion Γ Q hs)) (hc.map (inclusion_injective Γ Q hs))
      rwa [inclusion_weight] at hp)
  have hc : (Q.filter (fun d => degree Γ Q (Γ.origin d)≠2)).card≤R := by
    have he : (Finset.univ.filter (fun d : Q =>
        (DegreeTwoSuppression.out (restrict Γ Q hs).origin ((restrict Γ Q hs).origin d)).card≠2)).card =
        (Q.filter (fun d => degree Γ Q (Γ.origin d)≠2)).card := by
      simp only [restrict_degree]
      apply Finset.card_bij (fun d _ => d.val)
      · intro d hd; exact Finset.mem_filter.mpr ⟨d.property,(Finset.mem_filter.mp hd).2⟩
      · intro a _ b _ h; exact Subtype.ext h
      · intro d hd
        exact ⟨⟨d,(Finset.mem_filter.mp hd).1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hd).2⟩,rfl⟩
    rwa [he] at hbound
  have hpQ : potential Γ Q ≤ (R:ℤ) := by
    calc potential Γ Q ≤ ((∑ v : V, (if degree Γ Q v≠2 then degree Γ Q v else 0)):ℕ) := by
          rw [Nat.cast_sum]
          unfold potential
          apply Finset.sum_le_sum
          intro v hv
          simpa only [ite_not] using surplus_le_branch (degree Γ Q v)
      _ = ((Q.filter (fun d => degree Γ Q (Γ.origin d)≠2)).card:ℤ) := by
          rw [fiber_count]
      _ ≤ R := by exact_mod_cast hc
  have hex := excess_le_potential_add_leaves Γ Finset.univ
  have hle : (∑ v, (degree Γ Finset.univ v - 2))≤R+leaves := by
    have hl' : ((Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card:ℤ)≤leaves := by
      exact_mod_cast hl
    have hh : (((∑ v, (degree Γ Finset.univ v - 2)):ℕ):ℤ)≤(R:ℤ)+leaves := by omega
    exact_mod_cast hh
  exact (branch_degrees_bound_excess Γ Finset.univ).trans (Nat.mul_le_mul_left 3 hle)

end TorsionFreeZeroDivisors.ImageComplexity

namespace TorsionFreeZeroDivisors.SystemLeaves
open SimpleGraph PortSubdivision
open scoped Classical
variable {W : Type*} {G : SimpleGraph W}

/-- The combinatorial leaf condition, stated without assuming local finiteness. -/
def AtMostOneNeighbor (x : W) : Prop := ∀ a b, G.Adj x a → G.Adj x b → a=b

lemma leaf_in_reduced_walk {a b x : W} (p : G.Walk a b)
    (hr : p.edges.IsChain (· ≠ ·)) (hx : AtMostOneNeighbor (G := G) x)
    (hm : x∈p.support) : x=a ∨ x=b := by
  induction p with
  | nil => exact Or.inl (by simpa using hm)
  | @cons a c b h p ih =>
    by_cases he : x=a
    · exact Or.inl he
    have hm' : x∈p.support := by simpa only [Walk.support_cons,List.mem_cons,he,false_or] using hm
    have htail := (List.isChain_cons.mp hr).2
    rcases ih htail hm' with hec | heb
    · subst x
      cases p with
      | nil => exact Or.inr rfl
      | @cons c d b h' p =>
        have hda : d=a := hx d a h' h.symm
        subst d
        have hh := (List.isChain_cons_cons.mp hr).1
        exact False.elim (hh (Sym2.eq_swap))
    · exact Or.inr heb

/-- Including the closing turn, not just linear immersion. -/
def CyclicallyReduced {a : W} (p : G.Walk a a) : Prop :=
  p.edges.IsChain (· ≠ ·) ∧ (¬p.Nil → s(a,p.snd) ≠ s(p.penultimate,a))

lemma leaf_not_in_cyclic {a x : W} (p : G.Walk a a)
    (hr : CyclicallyReduced p) (hne : ¬p.Nil)
    (hx : AtMostOneNeighbor (G := G) x) : x∉p.support := by
  intro hm
  have he : x=a := (leaf_in_reduced_walk p hr.1 hx hm).elim id id
  subst x
  have heq : p.snd=p.penultimate := hx _ _ (p.adj_snd hne) (p.adj_penultimate hne).symm
  exact hr.2 hne (by rw [heq,Sym2.eq_swap])

variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)

def degree (v : V) : ℕ := (Finset.univ.filter (fun d => Γ.origin d=v)).card

lemma leaf_original (v : V) (hv : degree Γ v=1) :
    AtMostOneNeighbor (G := Γ.subdivision) (.inl v) := by
  intro a b ha hb
  rcases a with a|a <;> rcases b with b|b
  · exact False.elim ha
  · exact False.elim ha
  · exact False.elim hb
  · have hsingle := Finset.card_eq_one.mp hv
    obtain ⟨d,hd⟩ := hsingle
    have ha' : a∈Finset.univ.filter (fun e => Γ.origin e=v) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
    have hb' : b∈Finset.univ.filter (fun e => Γ.origin e=v) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩
    rw [hd] at ha' hb'
    exact congrArg Sum.inr ((Finset.mem_singleton.mp ha').trans (Finset.mem_singleton.mp hb').symm)

/-- In the actual image of any number of cyclically immersed closed walks and
one immersed interval, every leaf is an endpoint of that interval. -/
lemma actual_image_leaf_endpoints {J : Type*} (base : J → V)
    (loops : ∀ j, Γ.subdivision.Walk (.inl (base j)) (.inl (base j)))
    (hloops : ∀ j, CyclicallyReduced (loops j)) (hne : ∀ j, ¬(loops j).Nil)
    {a b : V} (p : Γ.subdivision.Walk (.inl a) (.inl b))
    (hp : p.edges.IsChain (· ≠ ·))
    (himage : ∀ d : D, Sum.inl (Γ.origin d)∈p.support ∨
      ∃ j, Sum.inl (Γ.origin d)∈(loops j).support)
    (v : V) (hv : degree Γ v=1) : v=a ∨ v=b := by
  have hpos : 0<(Finset.univ.filter (fun d => Γ.origin d=v)).card := by rw [← degree,hv]; decide
  obtain ⟨d,hd⟩ := Finset.card_pos.mp hpos
  have ho := (Finset.mem_filter.mp hd).2
  have hi := himage d
  rw [ho] at hi
  rcases hi with hi | ⟨j,hj⟩
  · have hh := leaf_in_reduced_walk p hp (leaf_original Γ v hv) hi
    exact hh.imp Sum.inl.inj Sum.inl.inj
  · exact False.elim (leaf_not_in_cyclic (loops j) (hloops j) (hne j) (leaf_original Γ v hv) hj)

variable [Fintype V]

lemma actual_image_at_most_two_leaves {J : Type*} (base : J → V)
    (loops : ∀ j, Γ.subdivision.Walk (.inl (base j)) (.inl (base j)))
    (hloops : ∀ j, CyclicallyReduced (loops j)) (hne : ∀ j, ¬(loops j).Nil)
    {a b : V} (p : Γ.subdivision.Walk (.inl a) (.inl b))
    (hp : p.edges.IsChain (· ≠ ·))
    (himage : ∀ d : D, Sum.inl (Γ.origin d)∈p.support ∨
      ∃ j, Sum.inl (Γ.origin d)∈(loops j).support) :
    (Finset.univ.filter (fun v => degree Γ v=1)).card≤2 := by
  classical
  calc (Finset.univ.filter (fun v => degree Γ v=1)).card ≤ ({a,b}:Finset V).card := by
        apply Finset.card_le_card
        intro v hv
        simpa only [Finset.mem_insert,Finset.mem_singleton] using
          actual_image_leaf_endpoints Γ base loops hloops hne p hp himage v (Finset.mem_filter.mp hv).2
    _ ≤ 2 := (Finset.card_insert_le a {b}).trans (by simp)

end TorsionFreeZeroDivisors.SystemLeaves

end

end OAI
