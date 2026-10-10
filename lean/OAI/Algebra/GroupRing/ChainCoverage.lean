import Mathlib
import OAI.Algebra.GroupRing.CoreStripping

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainCoverage
open Function ChainSuppression
open scoped Classical
variable {D : Type*} [Finite D] (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

/-- A dart lying in one of the actual maximal marked chains. -/
def Covered (d : D) : Prop :=
  ∃ (x : {x : D // τ x = x}) (i : Fin (length σ τ hσ hτ x.val x.property)),
    (next σ τ)^[i.val] x.val = d

lemma covered_fixed {d : D} (hd : τ d=d) : Covered σ τ hσ hτ d := by
  exact ⟨⟨d,hd⟩, ⟨0,length_pos σ τ hσ hτ d hd⟩,rfl⟩

lemma covered_next {d : D} (hd : Covered σ τ hσ hτ d) :
    Covered σ τ hσ hτ (next σ τ d) := by
  obtain ⟨x,i,rfl⟩ := hd
  by_cases hi : i.val+1 < length σ τ hσ hτ x.val x.property
  · refine ⟨x,⟨i.val+1,hi⟩,?_⟩
    exact iterate_succ_apply' _ _ _
  · have he : i.val+1 = length σ τ hσ hτ x.val x.property := by omega
    apply covered_fixed
    rw [← iterate_succ_apply' (next σ τ) i.val x.val]
    change τ ((next σ τ)^[i.val+1] x.val) = (next σ τ)^[i.val+1] x.val
    rw [he]
    exact length_fixed σ τ hσ hτ x.val x.property

/-- Reversing an original dart stays in the opposite oriented marked chain. -/
lemma covered_reverse {d : D} (hd : Covered σ τ hσ hτ d) :
    Covered σ τ hσ hτ (σ d) := by
  obtain ⟨x,i,rfl⟩ := hd
  let k := length σ τ hσ hτ x.val x.property
  let e := endpoint σ τ hσ hτ x
  have hi : i.val < k := i.isLt
  have hk : length σ τ hσ hτ e.val e.property=k := length_endpoint σ τ hσ hτ x
  have hj : k-i.val-1 < length σ τ hσ hτ e.val e.property := by omega
  refine ⟨e,⟨k-i.val-1,hj⟩,?_⟩
  have hf := endpoint_reverse σ τ hσ hτ (x:=x) (i:=k-i.val) (by omega)
  have he : k-(k-i.val)=i.val := by omega
  have hs : k-i.val=(k-i.val-1)+1 := by omega
  change (next σ τ)^[k-i.val] e.val = τ ((next σ τ)^[k-(k-i.val)] x.val) at hf
  rw [he,hs,iterate_succ_apply'] at hf
  have h := congrArg τ hf
  change τ (τ (σ ((next σ τ)^[k-i.val-1] e.val))) = τ (τ ((next σ τ)^[i.val] x.val)) at h
  rw [hτ,hτ] at h
  have hh := congrArg σ h
  rwa [hσ] at hh

end TorsionFreeZeroDivisors.ChainCoverage

namespace TorsionFreeZeroDivisors.ActualMarkedChains
open Function PortSubdivision ChainSuppression DegreeTwoSuppression ChainCoverage
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)

lemma forced_turn {d e : D} (hst : WeightedMoore.PortWalk.step Γ.origin Γ.reverse d e)
    (he : ¬mark (Γ.origin e)) :
    turn Γ.origin mark h2 (Γ.reverse d)=e := by
  have hd : ¬mark (Γ.origin (Γ.reverse d)) := hst.1 ▸ he
  apply (unique_other Γ.origin (Γ.reverse d) (h2 _ hd)).unique
  · exact turn_of_unmarked Γ.origin mark h2 (Γ.reverse d) hd
  · exact ⟨hst.1.symm,hst.2⟩

lemma covered_step {d e : D}
    (hd : Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d)
    (hst : WeightedMoore.PortWalk.step Γ.origin Γ.reverse d e) :
    Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) e := by
  by_cases he : mark (Γ.origin e)
  · exact covered_fixed _ _ _ _ (turn_of_mark Γ.origin mark h2 e he)
  · have hh := covered_next _ _ _ _ hd
    change Covered _ _ _ _ (turn Γ.origin mark h2 (Γ.reverse d)) at hh
    rwa [forced_turn Γ mark h2 hst he] at hh

lemma covered_path (p : List D)
    (hp : p.IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    (hh : ∀ d∈p.head?, Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d) :
    ∀ d∈p, Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ha := hh a (by simp)
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ha
    · apply ih hp.tail ?_ d hd
      cases p with
      | nil => simp
      | cons b p =>
        intro e he
        have heb : b=e := by simpa using he
        subst e
        exact covered_step Γ mark h2 ha (List.isChain_cons_cons.mp hp).1

/-- Every dart of the actual image belongs to a marked chain. No circle
component is dropped: a path start is marked in every component. -/
theorem actual_image_covered {J : Type*} (paths : J → List D)
    (hpaths : ∀ j, (paths j).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    (hstarts : ∀ j d, d∈(paths j).head? → mark (Γ.origin d))
    (himage : ∀ d : D, ∃ j, d∈paths j ∨ Γ.reverse d∈paths j) :
    ∀ d, Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d := by
  intro d
  obtain ⟨j,hj⟩ := himage d
  have hp := covered_path Γ mark h2 (paths j) (hpaths j) (by
    intro e he
    exact covered_fixed _ _ _ _ (turn_of_mark Γ.origin mark h2 e (hstarts j e he)))
  rcases hj with hj|hj
  · exact hp d hj
  · have hh := covered_reverse _ _ _ _ (hp (Γ.reverse d) hj)
    rwa [Γ.reverse_reverse d] at hh

/-- Exact length accounting after suppressing the actual image, rather than
only the inequality for a possibly incomplete set of marked components. -/
theorem actual_chain_total {J : Type*} (paths : J → List D)
    (hpaths : ∀ j, (paths j).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    (hstarts : ∀ j d, d∈(paths j).head? → mark (Γ.origin d))
    (himage : ∀ d : D, ∃ j, d∈paths j ∨ Γ.reverse d∈paths j) :
    ∑ d : {d : D // turn Γ.origin mark h2 d=d}, chainLength Γ mark h2 d = Fintype.card D := by
  have hsurj : Surjective (fun p : (d : {d : D // turn Γ.origin mark h2 d=d}) ×
        Fin (chainLength Γ mark h2 d) => (next Γ.reverse (turn Γ.origin mark h2))^[p.2.val] p.1.val) := by
    intro d
    obtain ⟨x,i,hi⟩ := actual_image_covered Γ mark h2 paths hpaths hstarts himage d
    exact ⟨⟨x,i⟩,hi⟩
  exact le_antisymm (chainLength_total Γ mark h2) (by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_le_of_surjective _ hsurj)

end TorsionFreeZeroDivisors.ActualMarkedChains

namespace TorsionFreeZeroDivisors.MarkedChainBound
open PortSubdivision DegreeTwoSuppression CoreStripping ImageComplexity
open scoped Classical BigOperators
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)

/-- Mark all irregular vertices and the specified
start/end vertices. -/
def marks (M : Finset V) (v : V) : Prop := degree Γ Finset.univ v ≠ 2 ∨ v∈M

omit [Fintype V] in
lemma marks_degree_two (M : Finset V) (v : V) (hv : ¬marks Γ M v) :
    (out Γ.origin v).card=2 := by
  change degree Γ Finset.univ v=2
  exact Classical.not_not.mp (fun h => hv (Or.inl h))

lemma marked_dart_bound (M : Finset V) :
    (Finset.univ.filter (fun d => marks Γ M (Γ.origin d))).card ≤
      (Finset.univ.filter (fun d => 3≤degree Γ Finset.univ (Γ.origin d))).card +
      (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card + 2*M.card := by
  rw [← fiber_count Γ Finset.univ (marks Γ M)]
  calc (∑ v, if marks Γ M v then degree Γ Finset.univ v else 0) ≤
      ∑ v, ((if 3≤degree Γ Finset.univ v then degree Γ Finset.univ v else 0) +
        (if degree Γ Finset.univ v=1 then 1 else 0) + (if v∈M then 2 else 0)) := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hb : 3 ≤ degree Γ Finset.univ v <;>
          by_cases hl : degree Γ Finset.univ v = 1 <;>
          by_cases hm : v ∈ M <;>
          simp_all [marks] <;> split_ifs <;> omega
    _ = (Finset.univ.filter (fun d => 3≤degree Γ Finset.univ (Γ.origin d))).card +
      (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card + 2*M.card := by
        rw [Finset.sum_add_distrib,Finset.sum_add_distrib,fiber_count]
        simp [Finset.sum_ite_mem,Nat.mul_comm]

omit [Fintype V] in
lemma chain_dart_card (M : Finset V) :
    Fintype.card {d : D // turn Γ.origin (marks Γ M) (marks_degree_two Γ M) d=d} =
      (Finset.univ.filter (fun d => marks Γ M (Γ.origin d))).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,turn_fixed_iff]

/-- Uniformly bounded many marked chains of the actual image, before choosing
any label assignments. The bound depends only on C and K. -/
theorem bounded_marked_chains (C : ℝ) (hC : 0≤C) (K : ℕ) :
    ∃ R : ℕ, ∀ {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)
      (L : ℝ) (_ : 0<L) (_ : (Fintype.card D:ℝ)≤2*C*L)
      (_ : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
        L≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1:ℝ))) c)
      (_ : (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card≤2)
      (M : Finset V) (_ : M.card≤2*K),
      Fintype.card {d : D // turn Γ.origin (marks Γ M) (marks_degree_two Γ M) d=d}≤R := by
  obtain ⟨R,hR⟩ := bounded_image_branches C hC 2
  refine ⟨R+2+4*K,?_⟩
  intro V D _ _ Γ L hL hsize hg hleaves M hM
  rw [chain_dart_card]
  have hb := marked_dart_bound Γ M
  have hr := hR Γ L hL hsize hg hleaves
  omega

end TorsionFreeZeroDivisors.MarkedChainBound

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore WeightedPortMoore SuppressedMoore ActualMarkedChains
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

/-- The literal nonempty word of original darts in one oriented marked chain. -/
def word (d : B) : List D := outWord (iterChain F (len d-1) d.val)

omit [Fintype D] in
lemma outWord_length {k : ℕ} (p : Chain D k) : (outWord p).length=k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [outWord,List.length_cons,Nat.succ_eq_add_one,Nat.add_right_cancel_iff] using ih p.2

omit [Fintype D] in
lemma outWord_last {k : ℕ} (p : Chain D k) : (outWord p).getLast?=some (last p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (p.1 :: outWord p.2).getLast? = some (last p.2)
    simp only [List.getLast?_cons,ih,Option.getD_some]

lemma word_length (d : B) : (word Γ mark h2 d).length=len d := by
  rw [word,outWord_length]
  have h := chainLength_pos Γ mark h2 d
  omega

lemma word_end (d : B) : ∀ e∈(word Γ mark h2 d).getLast?, mark (Γ.origin (Γ.reverse e)) := by
  intro e he
  rw [word,outWord_last] at he
  have he' : last (iterChain F (len d-1) d.val)=e := by simpa using he
  rw [←he',chain_last]
  exact (turn_fixed_iff Γ.origin mark h2 _).mp ((suppressed Γ mark h2).reverse d).property

/-- A reduced path cannot stop before the end of its current marked chain:
its prescribed last vertex is marked, while all interior chain vertices are not. -/
lemma iter_chain_prefix (n : ℕ) (x : D) (p : List D)
    (hp : p.IsChain (PortWalk.step Γ.origin Γ.reverse)) (hh : p.head?=some x)
    (ht : ∀ d∈p.getLast?, mark (Γ.origin (Γ.reverse d)))
    (hn : ∀ i : ℕ, 0 < i → i ≤ n → ¬mark (Γ.origin (F^[i] x))) :
    outWord (iterChain F n x) <+: p := by
  induction n generalizing x p with
  | zero =>
    cases p with
    | nil => simp at hh
    | cons a p =>
      have ha : a=x := Option.some.inj hh
      subst a
      exact ⟨p,rfl⟩
  | succ n ih =>
    cases p with
    | nil => simp at hh
    | cons a p =>
      have ha : a=x := Option.some.inj hh
      subst a
      cases p with
      | nil =>
        have ht' := ht x (by simp)
        have hu := hn 1 (by omega) (by omega)
        apply False.elim
        apply hu
        simpa only [iterate_one,next,comp_apply,turn_origin] using ht'
      | cons y p =>
        have hst := (List.isChain_cons_cons.mp hp).1
        have hy : ¬mark (Γ.origin y) := by
          have ho : Γ.origin (F x)=Γ.origin y := by
            exact (turn_origin Γ.origin mark h2 (Γ.reverse x)).trans hst.1
          have hu := hn 1 (by omega) (by omega)
          simpa only [iterate_one,ho] using hu
        have he : F x=y := forced_turn Γ mark h2 hst hy
        have htt : ∀ d∈(y::p).getLast?, mark (Γ.origin (Γ.reverse d)) := by
          simpa only [List.getLast?_cons_cons] using ht
        have hnn : ∀ i : ℕ, 0 < i → i ≤ n → ¬mark (Γ.origin (F^[i] y)) := by
          intro i hi hin
          have h := hn (i+1) (by omega) (by omega)
          simpa only [iterate_succ_apply,he] using h
        obtain ⟨q,hq⟩ := ih y (y::p) hp.tail rfl htt hnn
        refine ⟨q,?_⟩
        change x :: (outWord (iterChain F n (F x)) ++ q) = x :: y :: p
        rw [he,hq]

lemma word_prefix (d : B) (p : List D)
    (hp : p.IsChain (PortWalk.step Γ.origin Γ.reverse)) (hh : p.head?=some d.val)
    (ht : ∀ e∈p.getLast?, mark (Γ.origin (Γ.reverse e))) : word Γ mark h2 d <+: p := by
  apply iter_chain_prefix Γ mark h2 (len d-1) d.val p hp hh ht
  intro i hi hil
  rw [←turn_fixed_iff Γ.origin mark h2]
  apply no_internal_mark Γ.reverse τ Γ.reverse_reverse (turn_involutive Γ.origin mark h2)
    d.val d.property hi
  have h := chainLength_pos Γ mark h2 d
  change i<len d
  omega

/-- Every original path traverses whole marked chains.
This includes a path that returns to a mark, and does not require it embedded. -/
theorem path_decomposes (p : List D)
    (hp : p.IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hs : ∀ d∈p.head?, mark (Γ.origin d))
    (ht : ∀ d∈p.getLast?, mark (Γ.origin (Γ.reverse d))) :
    ∃ ds : List B, ds.flatMap (word Γ mark h2)=p := by
  cases p with
  | nil => exact ⟨[],rfl⟩
  | cons a p =>
    let d : B := ⟨a, turn_of_mark Γ.origin mark h2 a (hs a (by simp))⟩
    obtain ⟨r,hr⟩ := word_prefix Γ mark h2 d (a::p) hp rfl ht
    have hparts := List.isChain_append.mp (hr.symm ▸ hp)
    have hsr : ∀ b∈r.head?, mark (Γ.origin b) := by
      intro b hb
      let e := last (iterChain F (len d-1) d.val)
      have he : e∈(word Γ mark h2 d).getLast? := by
        rw [word,outWord_last]
        exact rfl
      have hstep := hparts.2.2 e he b hb
      exact hstep.1 ▸ word_end Γ mark h2 d e he
    have htr : ∀ b∈r.getLast?, mark (Γ.origin (Γ.reverse b)) := by
      intro b hb
      have hrne : r≠[] := by intro he; simp [he] at hb
      apply ht b
      rw [←hr,List.getLast?_append_of_ne_nil _ hrne]
      exact hb
    have hlen : r.length < (a::p).length := by
      have h := congrArg List.length hr
      simp only [List.length_append,word_length] at h
      have hd := chainLength_pos Γ mark h2 d
      omega
    obtain ⟨ds,hds⟩ := path_decomposes r hparts.2.1 hsr htr
    refine ⟨d::ds,?_⟩
    simpa only [List.flatMap_cons,hds] using hr
termination_by p.length

omit [Fintype D] in
/-- Enumerating a chain lists precisely the forward iterates before its first mark. -/
lemma outWord_iterChain (f : D → D) (n : ℕ) (x : D) :
    outWord (iterChain f n x) = (List.range (n+1)).map (fun i => f^[i] x) := by
  induction n generalizing x with
  | zero => simp [iterChain,outWord]
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [iterChain,outWord,ih,List.map_cons,List.map_map,iterate_zero,id_eq]
    congr 1

lemma word_eq_range (d : B) :
    word Γ mark h2 d = (List.range (len d)).map (fun i => F^[i] d.val) := by
  rw [word,outWord_iterChain]
  have h := chainLength_pos Γ mark h2 d
  congr 2
  omega

lemma mem_word_iff (d : B) (x : D) :
    x∈word Γ mark h2 d ↔ ∃ i : Fin (len d), F^[i.val] d.val=x := by
  rw [word_eq_range,List.mem_map]
  constructor
  · rintro ⟨i,hi,hx⟩
    exact ⟨⟨i,List.mem_range.mp hi⟩,hx⟩
  · rintro ⟨i,hx⟩
    exact ⟨i.val,List.mem_range.mpr i.isLt,hx⟩

lemma word_nodup (d : B) : (word Γ mark h2 d).Nodup := by
  rw [word_eq_range]
  apply List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj he
  have h := chain_dart_injective Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2)
    (a₁ := ⟨d,⟨i,List.mem_range.mp hi⟩⟩)
    (a₂ := ⟨d,⟨j,List.mem_range.mp hj⟩⟩) he
  exact congrArg (fun p => p.2.val) h

lemma words_disjoint {d e : B} (hne : d≠e) :
    List.Disjoint (word Γ mark h2 d) (word Γ mark h2 e) := by
  intro x hx hy
  obtain ⟨i,hi⟩ := (mem_word_iff Γ mark h2 d x).mp hx
  obtain ⟨j,hj⟩ := (mem_word_iff Γ mark h2 e x).mp hy
  have h := chain_dart_injective Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) (a₁ := ⟨d,i⟩) (a₂ := ⟨e,j⟩) (hi.trans hj.symm)
  exact hne (congrArg Sigma.fst h)

lemma count_word (d e : B) (x : D) (hx : x∈word Γ mark h2 d) :
    (word Γ mark h2 e).count x = if e=d then 1 else 0 := by
  by_cases he : e=d
  · subst e
    simpa using List.count_eq_one_of_mem (word_nodup Γ mark h2 d) hx
  · have hnot : x∉word Γ mark h2 e := by
      intro hy
      exact words_disjoint Γ mark h2 he hy hx
    simp [he,List.count_eq_zero.mpr hnot]

/-- Every directed edge in one chain has the same traversal multiplicity,
namely the number of occurrences of that oriented chain in the decomposition. -/
lemma multiplicity_constant (ds : List B) (d : B) (x : D)
    (hx : x∈word Γ mark h2 d) :
    (ds.flatMap (word Γ mark h2)).count x = ds.count d := by
  induction ds with
  | nil => rfl
  | cons e ds ih =>
    simp only [List.flatMap_cons,List.count_append,count_word Γ mark h2 d e x hx,ih]
    by_cases he : e=d <;> simp [he,Nat.add_comm]

end TorsionFreeZeroDivisors.ChainPaths

end

end OAI
