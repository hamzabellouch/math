import OAI.Probability.FKMaps.PlanarActivity
import OAI.Probability.FKMaps.WordMaps

namespace OAI

noncomputable section
open Set Equiv Equiv.Perm
namespace FKCRT
variable {n : ℕ}

lemma oneCycle_isCycleOn (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e) :
    p.IsCycleOn (Finset.univ : Finset (Dart n)) :=
  ⟨by simp, fun _ _ _ _ => h _ _⟩

lemma oneCycle_numbering_bijective (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e) :
    Function.Bijective (fun i : Dart n => (p^i.val) 0) := by
  have hh := oneCycle_isCycleOn p h
  constructor
  · intro i j hij
    have hm := (hh.pow_apply_eq_pow_apply (Finset.mem_univ (0 : Dart n))).mp hij
    have hm' : i.val % (2*(n+1)) = j.val % (2*(n+1)) := by
      simpa only [Finset.card_univ,Fintype.card_fin,Nat.ModEq] using hm
    rw [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at hm'
    exact Fin.ext hm'
  · intro d
    obtain ⟨k,hk,hkd⟩ := hh.exists_pow_eq (Finset.mem_univ (0 : Dart n)) (Finset.mem_univ d)
    refine ⟨⟨k,?_⟩,hkd⟩
    simpa only [Finset.card_univ,Fintype.card_fin] using hk

/-- Tour positions with initial position the original root dart. -/
def tourNumbering (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e) : Perm (Dart n) :=
  Equiv.ofBijective _ (oneCycle_numbering_bijective p h)

@[simp] lemma tourNumbering_apply (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e)
    (i : Dart n) : tourNumbering p h i = (p^i.val) 0 := rfl

@[simp] lemma tourNumbering_zero (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e) :
    tourNumbering p h 0 = 0 := by simp

lemma tourNumbering_successor (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e)
    (i : Dart n) :
    tourNumbering p h (finRotate (2*(n+1)) i) = p (tourNumbering p h i) := by
  simp only [tourNumbering_apply]
  rw [← mul_apply p (p^i.val),← pow_succ']
  apply (oneCycle_isCycleOn p h).pow_apply_eq_pow_apply (Finset.mem_univ (0 : Dart n)) |>.mpr
  simp only [Finset.card_univ,Fintype.card_fin] at ⊢
  change (finRotate (2*(n+1)) i).val % (2*(n+1)) = (i.val+1) % (2*(n+1))
  have hi : (finRotate (2*(n+1)) i).val = (i.val+1) % (2*(n+1)) := by
    rw [finRotate_apply,Fin.val_add]
    congr 1
  rw [hi,Nat.mod_mod]

/-- The root-preserving numbering is uniquely determined by the tour. -/
lemma tourNumbering_unique (p : Perm (Dart n)) (h : ∀ d e,p.SameCycle d e)
    (r : Perm (Dart n)) (hr : r 0=0)
    (hp : ∀ i,r (finRotate (2*(n+1)) i)=p (r i)) : r=tourNumbering p h := by
  apply Equiv.ext
  intro i
  have hrot : ∀ (k : ℕ) (hk : k<2*(n+1)), ((finRotate (2*(n+1)))^k) 0 = (⟨k,hk⟩ : Dart n) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ',mul_apply,ih (by omega),finRotate_apply]
      apply Fin.ext
      simp only [Fin.val_add]
      simp [Nat.mod_eq_of_lt (by omega : k+1<2*(n+1)),Nat.mod_eq_of_lt (by omega : 1<2*(n+1))]
  have he (k : ℕ) : r (((finRotate (2*(n+1)))^k) 0) = (p^k) 0 := by
    induction k with
    | zero => exact hr
    | succ k ih => rw [pow_succ',mul_apply,hp,ih,pow_succ',mul_apply]
  simpa only [hrot i.val i.isLt,tourNumbering_apply] using he i.val

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- Source exploration: start at the root and follow decided tree/non-tree
rules until the first as-yet undecided edge. The fallback is only for states
without a spanning-tree completion; it is never used on a valid branch. -/
def tourSelector (a s : Perm (Dart n)) (ha : Function.Involutive a) : EdgeSelector a := fun C R hR =>
  if h : ∃ k : ℕ,orbit a (((s*partialReversal a ha C)^k) 0)∈R then
    ⟨orbit a (((s*partialReversal a ha C)^(Nat.find h)) 0),Nat.find_spec h⟩
  else ⟨hR.choose,hR.choose_spec⟩

lemma partial_tour_eq_outside (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hC : C⊆T) (hT : T⊆C∪R) (d : Dart n)
    (hd : orbit a d∉R) : (s*partialReversal a ha C) d=(s*partialReversal a ha T) d := by
  have hh : orbit a d∈C ↔ orbit a d∈T := ⟨fun h => hC h,fun h => by
    rcases Finset.mem_union.mp (hT h) with h|h
    · exact h
    · exact False.elim (hd h)⟩
  simp only [mul_apply,partialReversal_apply,hh]

lemma partial_tour_prefix (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hC : C⊆T) (hT : T⊆C∪R) (k : ℕ)
    (hk : ∀ j<k,orbit a (((s*partialReversal a ha T)^j) 0)∉R) :
    ((s*partialReversal a ha C)^k) 0=((s*partialReversal a ha T)^k) 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',mul_apply,ih (fun j hj => hk j (by omega)),pow_succ',mul_apply]
    exact partial_tour_eq_outside a s ha C R T hC hT _ (hk k (by omega))

/-- The next chosen edge is exactly the first undecided edge of *every*
completed tree tour. In particular it depends only on previous choices. -/
theorem tourSelector_first (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hR : R.Nonempty) (hC : C⊆T) (hT : T⊆C∪R)
    (ht : ∀ d e,(s*partialReversal a ha T).SameCycle d e) :
    ∃ k : ℕ, orbit a (((s*partialReversal a ha T)^k) 0)=(tourSelector a s ha C R hR).val ∧
      orbit a (((s*partialReversal a ha T)^k) 0)∈R ∧
      ∀ j<k,orbit a (((s*partialReversal a ha T)^j) 0)∉R := by
  have hex : ∃ k : ℕ,orbit a (((s*partialReversal a ha T)^k) 0)∈R := by
    obtain ⟨e,he⟩ := hR
    obtain ⟨k,hk⟩ := (ht 0 e.out).exists_nat_pow_eq
    exact ⟨k,by rw [hk,show orbit a e.out=e from Quotient.out_eq e]; exact he⟩
  let k := Nat.find hex
  have hk : orbit a (((s*partialReversal a ha T)^k) 0)∈R := Nat.find_spec hex
  have hlt : ∀ j<k,orbit a (((s*partialReversal a ha T)^j) 0)∉R :=
    fun j hj => Nat.find_min hex hj
  have heq := partial_tour_prefix a s ha C R T hC hT k hlt
  have hex' : ∃ j : ℕ,orbit a (((s*partialReversal a ha C)^j) 0)∈R :=
    ⟨k,by rw [heq]; exact hk⟩
  have hfind : Nat.find hex'=k := by
    apply le_antisymm (Nat.find_min' hex' (by rw [heq]; exact hk))
    by_contra hh
    have hj : Nat.find hex'<k := by omega
    have heq' := partial_tour_prefix a s ha C R T hC hT (Nat.find hex') (fun i hi => hlt i (lt_trans hi hj))
    exact hlt _ hj (heq' ▸ Nat.find_spec hex')
  refine ⟨k,?_,hk,hlt⟩
  simp only [tourSelector,dite_eq_left hex',hfind,heq]

lemma treeExtension_tour (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (h : T∈treeExtensions a s C R) :
    ∀ d e,(s*partialReversal a ha T).SameCycle d e := by
  have hh := (mem_treeExtensions a s C R T).mp h
  intro d e
  exact (hh.2.2.1.sameCycle_iff_reachable ha d e).mpr (hh.2.2.2.preconnected _ _)

/-- Exact rooted-tour adaptive expansion of the finite FK loop polynomial. -/
theorem loopPolynomial_tour_activity (t : ℝ) (ht : t≠0) (M : RootedMap n) :
    loopPolynomial t M = ∑ T∈treeExtensions (reversal M) (rotation M) ∅ Finset.univ,
      (1+t)^explorationActivity (reversal M) (rotation M)
        (tourSelector (reversal M) (rotation M) M.out.property.1) ∅ Finset.univ T (n+1) := by
  rw [← residualPartition_initial]
  apply adaptive_activity_expansion t ht (reversal M) (rotation M) M.out.property.1
  · rw [Finset.card_univ,reversal_card (reversal M) M.out.property.1 M.out.property.2.1]
  · simp
  · refine ⟨?_,by simp,?_⟩
    · have he : spanningGraph (reversal M) (rotation M) (∅ : Finset (Edge M))=⊥ := by
        ext v w
        simp [spanningGraph]
      rw [he]
      exact SimpleGraph.isAcyclic_bot
    · intro e he
      simp at he
  · convert M.out.property.2.2.1 using 1
    congr 1
    apply heq_of_eq
    congr 1
    ext e
    simp
    trivial

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma Multiforest.edgeEnds_mem_iff {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {A T : Finset (Orbit a)} (h : Multiforest a s T) (hA : A⊆T)
    {e : Orbit a} (he : e∈T) :
    edgeEnds a s e∈(spanningGraph a s (A : Set (Orbit a))).edgeSet ↔ e∈A := by
  constructor
  · intro hh
    obtain ⟨f,hf,hfe⟩ := spanningGraph_edgeSet_subset a s ha A hh
    have hfe' := h.2.2 (hA hf) he hfe
    exact hfe' ▸ hf
  · intro heA
    apply (SimpleGraph.mem_edgeSet _).mpr
    refine ⟨h.2.1 e he,Or.inl ⟨e.out,?_,rfl,rfl⟩⟩
    change orbit a e.out∈A
    simpa only [show orbit a e.out=e from Quotient.out_eq e] using heA

/-- A subtree connects two vertices precisely when it retains every edge of
 their unique tree path, expressed without choosing that path. -/
theorem Multiforest.reachable_iff_all_cuts {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {C T : Finset (Orbit a)} (h : Multiforest a s T) (hC : C⊆T)
    (hc : (spanningGraph a s (T : Set (Orbit a))).Connected) (u v : Orbit s) :
    (spanningGraph a s (C : Set (Orbit a))).Reachable u v ↔
      ∀ e∈T, e∉C → (spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable u v := by
  constructor
  · intro hr e _ he
    apply hr.mono (spanningGraph_mono a s _)
    intro f hf
    exact Finset.mem_erase.mpr ⟨fun hfe => he (hfe ▸ hf),hC hf⟩
  · intro hall
    let G := spanningGraph a s (T : Set (Orbit a))
    have ht : G.IsTree := ⟨hc,h.1⟩
    obtain ⟨p,hp,hunique⟩ := ht.existsUnique_path u v
    suffices htransfer : ∀ z∈p.edges,z∈(spanningGraph a s (C : Set (Orbit a))).edgeSet from
      (p.transfer _ htransfer).reachable
    intro z hz
    obtain ⟨e,he,rfl⟩ := spanningGraph_edgeSet_subset a s ha T (p.edges_subset_edgeSet hz)
    apply (h.edgeEnds_mem_iff ha hC he).mpr
    by_contra heC
    let q := (hall e he heC).some.toPath
    have hle := spanningGraph_mono a s (show (T.erase e : Set (Orbit a))⊆(T : Set (Orbit a)) from Finset.erase_subset _ _)
    have hq : (q.val.mapLe hle).IsPath := q.property.mapLe hle
    have heq := hunique _ hq
    have hez : edgeEnds a s e∈(q.val.mapLe hle).edges := heq ▸ hz
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hez
    have hh := q.val.edges_subset_edgeSet hez
    exact Finset.notMem_erase e T ((h.edgeEnds_mem_iff ha (Finset.erase_subset _ _) he).mp hh)

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma spanningGraph_reachable_mono_relation (a s : Perm (Dart n))
    (ha : Function.Involutive a) (A B : Finset (Orbit a))
    (h : ∀ e∈B,(spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)))
    {u v : Orbit s} (hr : (spanningGraph a s (B : Set (Orbit a))).Reachable u v) :
    (spanningGraph a s (A : Set (Orbit a))).Reachable u v := by
  apply SimpleGraph.ConnectedComponent.eq.mp
  apply GraphMerge.reachable_eq_of_adj_eq _ _ _ hr
  intro x y hxy
  obtain ⟨e,he,heq⟩ := spanningGraph_edgeSet_subset a s ha B ((SimpleGraph.mem_edgeSet _).mpr hxy)
  have hh := h e he
  rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩|⟨h1,h2⟩
  · exact SimpleGraph.ConnectedComponent.sound (h1 ▸ h2 ▸ hh)
  · exact SimpleGraph.ConnectedComponent.sound (h2 ▸ h1 ▸ hh.symm)

lemma Multiforest.erase_components_two {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {T : Finset (Orbit a)} (h : Multiforest a s T)
    (hc : (spanningGraph a s (T : Set (Orbit a))).Connected) {e : Orbit a} (he : e∈T) :
    submapComponents a s (T.erase e)=2 := by
  have h1 := h.components_card ha
  have h2 := (h.mono (Finset.erase_subset e T)).components_card ha
  have hcard : submapComponents a s T=1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    exact ⟨hc.preconnected.subsingleton_connectedComponent,⟨(spanningGraph a s (T : Set _)).connectedComponentMk (orbit s 0)⟩⟩
  rw [Finset.card_erase_of_mem he] at h2
  have hp := Finset.card_pos.mpr ⟨e,he⟩
  omega

lemma Multiforest.erase_component_dichotomy {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {T : Finset (Orbit a)} (h : Multiforest a s T)
    (hc : (spanningGraph a s (T : Set (Orbit a))).Connected) {e : Orbit a} (he : e∈T)
    (v : Orbit s) :
    (spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable v (orbit s e.out) ∨
    (spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable v (orbit s (a e.out)) := by
  let G := spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))
  let x := G.connectedComponentMk (orbit s e.out)
  let y := G.connectedComponentMk (orbit s (a e.out))
  have hne : y≠x := by
    intro hh
    have hf : Multiforest a s (Insert.insert e (T.erase e)) := by rwa [Finset.insert_erase he]
    exact hf.insert_not_reachable ha (Finset.notMem_erase _ _) (SimpleGraph.ConnectedComponent.eq.mp hh.symm)
  have hh : Nat.card G.ConnectedComponent=2 := h.erase_components_two ha hc he
  obtain ⟨z,hz,hzu⟩ := (Nat.card_eq_two_iff' x).mp hh
  have hy : y=z := hzu y hne
  by_cases hv : G.connectedComponentMk v=x
  · exact Or.inl (SimpleGraph.ConnectedComponent.eq.mp hv)
  · exact Or.inr (SimpleGraph.ConnectedComponent.eq.mp ((hzu _ hv).trans hy.symm))

/-- A residual edge is a bridge exactly when no retained edge crosses its
fundamental tree cut. No simplicity assumption on the original map. -/
theorem Multiforest.residual_bridge_iff {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {T B : Finset (Orbit a)} (h : Multiforest a s T)
    (hc : (spanningGraph a s (T : Set (Orbit a))).Connected) {e : Orbit a} (he : e∈T)
    (hB : T.erase e⊆B) :
    ¬(spanningGraph a s (B : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) ↔
      ∀ f∈B,(spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable
        (orbit s f.out) (orbit s (a f.out)) := by
  let G := spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))
  constructor
  · intro hn f hf
    have hsub := spanningGraph_mono a s hB
    have hfr := spanningGraph_edge_reachable a s B f hf
    rcases h.erase_component_dichotomy ha hc he (orbit s f.out) with hf1|hf1 <;>
      rcases h.erase_component_dichotomy ha hc he (orbit s (a f.out)) with hf2|hf2
    · exact hf1.trans hf2.symm
    · exact False.elim (hn ((hf1.symm.mono hsub).trans (hfr.trans (hf2.mono hsub))))
    · exact False.elim (hn ((hf2.symm.mono hsub).trans (hfr.symm.trans (hf1.mono hsub))))
    · exact hf1.trans hf2.symm
  · intro hall hr
    have hf : Multiforest a s (Insert.insert e (T.erase e)) := by rwa [Finset.insert_erase he]
    exact hf.insert_not_reachable ha (Finset.notMem_erase _ _)
      (spanningGraph_reachable_mono_relation a s ha (T.erase e) B hall hr)

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- Symmetric fundamental-cut incidence. For distinct edges of a planar tree
tour this is precisely alternation of their two darts. -/
def FundamentalCross (a s : Perm (Dart n)) (T : Finset (Orbit a)) (e f : Orbit a) : Prop :=
  (e∈T ∧ ¬(spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s f.out) (orbit s (a f.out))) ∨
  (f∈T ∧ ¬(spanningGraph a s ((T.erase f : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out)))

lemma fundamentalCross_symm (a s : Perm (Dart n)) (T : Finset (Orbit a)) (e f : Orbit a) :
    FundamentalCross a s T e f ↔ FundamentalCross a s T f e := or_comm

lemma fundamentalCross_tree (a s : Perm (Dart n)) (T : Finset (Orbit a))
    {e f : Orbit a} (he : e∈T) (hne : e≠f) :
    FundamentalCross a s T e f ↔
      ¬(spanningGraph a s ((T.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable
        (orbit s f.out) (orbit s (a f.out)) := by
  constructor
  · rintro (h|h)
    · exact h.2
    · exact False.elim (h.2 (spanningGraph_edge_reachable a s (T.erase f) e (Finset.mem_erase.mpr ⟨hne,he⟩)))
  · exact fun h => Or.inl ⟨he,h⟩

lemma fundamentalCross_nontree (a s : Perm (Dart n)) (T : Finset (Orbit a))
    {e f : Orbit a} (he : e∉T) :
    FundamentalCross a s T e f ↔ f∈T ∧
      ¬(spanningGraph a s ((T.erase f : Finset (Orbit a)) : Set (Orbit a))).Reachable
        (orbit s e.out) (orbit s (a e.out)) := by
  simp only [FundamentalCross,he,false_and,false_or]

/-- Exact non-tree forced-loop condition, in terms of the undecided edges. -/
theorem treeExtension_loop_iff_no_cross (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hT : T∈treeExtensions a s C R) (hd : Disjoint C R)
    {e : Orbit a} (he : e∉T) :
    (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) ↔
      ∀ f∈R,¬FundamentalCross a s T e f := by
  obtain ⟨hCT,hTR,hf,hc⟩ := (mem_treeExtensions a s C R T).mp hT
  rw [hf.reachable_iff_all_cuts ha hCT hc]
  constructor
  · intro hh f hfR hfc
    rw [fundamentalCross_nontree a s T he] at hfc
    exact hfc.2 (hh f hfc.1 (fun hfC => Finset.disjoint_left.mp hd hfC hfR))
  · intro hh f hfT hfC
    have hfR : f∈R := (Finset.mem_union.mp (hTR hfT)).resolve_left hfC
    by_contra hn
    exact hh f hfR ((fundamentalCross_nontree a s T he).mpr ⟨hfT,hn⟩)

/-- Exact tree forced-bridge condition. The contracted/deleted state is the
one used by the genuine adaptive FK polynomial recursion. -/
theorem treeExtension_bridge_iff_no_cross (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hT : T∈treeExtensions a s C R) (hd : Disjoint C R)
    {e : Orbit a} (he : e∈T) (heR : e∈R) :
    ¬(spanningGraph a s ((C∪R.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out)) ↔
      ∀ f∈R.erase e,¬FundamentalCross a s T e f := by
  obtain ⟨hCT,hTR,hf,hc⟩ := (mem_treeExtensions a s C R T).mp hT
  have hsub : T.erase e⊆C∪R.erase e := by
    intro f hfT
    obtain ⟨hne,hfT⟩ := Finset.mem_erase.mp hfT
    rcases Finset.mem_union.mp (hTR hfT) with hh|hh
    · exact Finset.mem_union_left _ hh
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne,hh⟩)
  rw [hf.residual_bridge_iff ha hc he hsub]
  constructor
  · intro hh f hfR hcross
    have hne : e≠f := (Finset.mem_erase.mp hfR).1.symm
    exact (fundamentalCross_tree a s T he hne).mp hcross (hh f (Finset.mem_union_right _ hfR))
  · intro hh f hfB
    rcases Finset.mem_union.mp hfB with hfC|hfR
    · apply spanningGraph_edge_reachable a s (T.erase e) f
      refine Finset.mem_erase.mpr ⟨?_,hCT hfC⟩
      intro hfe
      exact Finset.disjoint_left.mp hd (hfe ▸ hfC) heR
    · have hne : e≠f := (Finset.mem_erase.mp hfR).1.symm
      by_contra hn
      exact hh f hfR ((fundamentalCross_tree a s T he hne).mpr hn)

lemma fundamental_cut_tour (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (e : Orbit a) (he : e∈T) :
    s*partialReversal a ha (T.erase e)=(s*partialReversal a ha T)*swap e.out (a e.out) := by
  have hh := partialReversal_insert a ha (T.erase e) e (Finset.notMem_erase _ _)
  rw [Finset.insert_erase he] at hh
  rw [hh]
  simp [mul_assoc]

/-- Fundamental tree cuts are exactly the two cycles obtained by cutting the
tour at the two darts of that edge. This is the algebraic contour-cut identity. -/
theorem fundamentalCross_tour_cut (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (hT : Multiforest a s T) {e f : Orbit a}
    (he : e∈T) (hne : e≠f) :
    FundamentalCross a s T e f ↔
      ¬((s*partialReversal a ha T)*swap e.out (a e.out)).SameCycle f.out (a f.out) := by
  rw [fundamentalCross_tree a s T he hne,← fundamental_cut_tour a s ha T e he]
  exact not_congr ((hT.mono (Finset.erase_subset _ _)).sameCycle_iff_reachable ha _ _).symm

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma disjoint_formPerm_action (U V : List α) (hn : (U++V).Nodup) :
    (∀ x∈U,(U.formPerm*V.formPerm) x=U.formPerm x) ∧
      (∀ x∈V,(U.formPerm*V.formPerm) x=V.formPerm x) := by
  have hd := List.disjoint_iff_ne.mpr (List.nodup_append.mp hn).2.2
  constructor
  · intro x hx
    rw [mul_apply,List.formPerm_apply_of_notMem (fun h => List.disjoint_left.mp hd hx h)]
  · intro x hx
    rw [mul_apply,List.formPerm_apply_of_notMem (fun h =>
      List.disjoint_left.mp hd h (V.formPerm_apply_mem_of_mem hx))]

lemma disjoint_formPerm_sameCycle (U V : List α) (hn : (U++V).Nodup)
    (hc : ∀ x,x∈U++V) (x y : α) :
    (U.formPerm*V.formPerm).SameCycle x y ↔ (x∈U ↔ y∈U) := by
  have ⟨hU,hV⟩ := disjoint_formPerm_action U V hn
  have hd := List.disjoint_iff_ne.mpr (List.nodup_append.mp hn).2.2
  constructor
  · intro h
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
      exact hk ▸ (pow_eq_on_list _ U hU hx k).2
    · intro hy
      obtain ⟨k,hk⟩ := h.symm.exists_nat_pow_eq
      exact hk ▸ (pow_eq_on_list _ U hU hy k).2
  · intro hh
    by_cases hx : x∈U
    · exact sameCycle_of_list _ hn.of_append_left hU hx (hh.mp hx)
    · have hy : y∉U := fun h => hx (hh.mpr h)
      exact sameCycle_of_list _ hn.of_append_right hV
        ((List.mem_append.mp (hc x)).resolve_left hx)
        ((List.mem_append.mp (hc y)).resolve_left hy)

/-- Cutting a cyclic tour at x,z separates precisely its two contour
intervals, including intervals with no interior darts. -/
theorem swap_tour_sameCycle (p : Perm α) (x z : α) (L R : List α)
    (he : orbitList p x=x::(L++z::R)) (hc : ∀ d e,p.SameCycle d e) (y w : α) :
    (swap x z*p).SameCycle y w ↔ (y∈x::L ↔ w∈x::L) := by
  have hn := nodup_orbitList p x
  rw [he] at hn
  have hp : p=(x::(L++z::R)).formPerm := by
    apply Equiv.ext
    intro d
    have hd := (mem_orbitList p x d).mpr (hc x d)
    simpa only [he] using orbitList_action p x d hd
  rw [hp,swap_mul_formPerm_cut x z L R hn]
  apply disjoint_formPerm_sameCycle _ _ hn
  intro d
  simpa only [he,List.cons_append] using (mem_orbitList p x d).mpr (hc x d)

/-- Right and left cuts have the same partition on darts other than the two
cut endpoints, which is exactly what is needed for distinct paired edges. -/
theorem tour_swap_sameCycle (p : Perm α) (x z : α) (L R : List α)
    (he : orbitList p x=x::(L++z::R)) (hc : ∀ d e,p.SameCycle d e)
    (y w : α) (hyx : y≠x) (hyz : y≠z) (hwx : w≠x) (hwz : w≠z) :
    (p*swap x z).SameCycle y w ↔ (y∈L ↔ w∈L) := by
  have hconj : p*swap x z=swap x z*(swap x z*p)*(swap x z)⁻¹ := by
    simp [← mul_assoc]
  rw [hconj,sameCycle_conj]
  simp only [swap_inv,swap_apply_of_ne_of_ne hyx hyz,swap_apply_of_ne_of_ne hwx hwz]
  rw [swap_tour_sameCycle p x z L R he hc y w]
  simp only [List.mem_cons,hyx,hwx,false_or]

end FKCRT.MapCycles
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [Fintype α] [LinearOrder α]

omit [Fintype α] in
lemma ordered_two_sublist {l : List α} (hs : l.Pairwise (·<·))
    {x z : α} (hx : x∈l) (hz : z∈l) (hxz : x<z) : [x,z]<+l := by
  apply List.sublist_of_subperm_of_pairwise (r := (·≤·))
  · apply List.subperm_of_subset (by simpa using ne_of_lt hxz)
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> assumption
  · simpa using le_of_lt hxz
  · exact hs.imp (fun h => le_of_lt h)

omit [Fintype α] in
lemma ordered_middle {U L R : List α} {x z y : α}
    (hs : (U++x::(L++z::R)).Pairwise (·<·))
    (hy : y∈U++x::(L++z::R)) : y∈L ↔ x<y ∧ y<z := by
  have hU := (List.pairwise_append.mp hs).2.2
  have hx := (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1
  have hLR := (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).2
  have hL := (List.pairwise_append.mp hLR).2.2
  have hz := (List.pairwise_cons.mp (List.pairwise_append.mp hLR).2.1).1
  constructor
  · intro hyL
    exact ⟨hx y (List.mem_append_left _ hyL),hL y hyL z (by simp)⟩
  · rintro ⟨hxy,hyz⟩
    simp only [List.mem_append,List.mem_cons] at hy
    rcases hy with hyU|rfl|hyL|rfl|hyR
    · exact False.elim ((not_lt_of_ge (hU y hyU x (by simp)).le) hxy)
    · exact False.elim ((lt_irrefl _) hxy)
    · exact hyL
    · exact False.elim ((lt_irrefl _) hyz)
    · exact False.elim ((not_lt_of_ge (hz y hyR).le) hyz)

/-- An ordered cyclic tour, cut at x<z, separates the strict linear interval
(x,z) from its complement, on all other darts. -/
theorem ordered_tour_cut (l : List α) (hs : l.Pairwise (·<·)) (hc : ∀ x,x∈l)
    (x z : α) (hxz : x<z) (y w : α)
    (hyx : y≠x) (hyz : y≠z) (hwx : w≠x) (hwz : w≠z) :
    (l.formPerm*swap x z).SameCycle y w ↔ ((x<y ∧ y<z) ↔ (x<w ∧ w<z)) := by
  have hn : l.Nodup := hs.imp (fun h => ne_of_lt h)
  have hsub := ordered_two_sublist hs (hc x) (hc z) hxz
  obtain ⟨U,K,hK,hsub⟩ := cons_sublist_split hsub
  obtain ⟨L,R,hR,_⟩ := cons_sublist_split hsub
  have he : l=U++x::(L++z::R) := by rw [hK,hR]
  have hp : l.formPerm=(x::(L++z::(R++U))).formPerm := by
    rw [he,formPerm_append_comm U _ (he ▸ hn)]
    simp only [List.cons_append,List.append_assoc]
  have hrot : orbitList l.formPerm x=x::(L++z::(R++U)) := by
    rw [hp,orbitList_formPerm]
    have hh := (List.perm_append_comm (l₁ := U) (l₂ := x::(L++z::R))).nodup_iff.mp (he ▸ hn)
    simpa only [List.cons_append,List.append_assoc] using hh
  have hcycle : ∀ d e,l.formPerm.SameCycle d e := by
    intro d e
    exact sameCycle_of_list _ hn (fun _ _ => rfl) (hc d) (hc e)
  rw [tour_swap_sameCycle l.formPerm x z L (R++U) hrot hcycle y w hyx hyz hwx hwz]
  exact iff_congr (ordered_middle (he ▸ hs) (he ▸ hc y)) (ordered_middle (he ▸ hs) (he ▸ hc w))

end FKCRT.MapCycles
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- First occurrence of an edge in a fixed rooted one-cycle tour. -/
def edgeFirst (a p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e) (e : Orbit a) : ℕ :=
  min ((tourNumbering p hp).symm e.out).val ((tourNumbering p hp).symm (a e.out)).val

lemma edgeFirst_lt (a p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e) (e : Orbit a) :
    edgeFirst a p hp e<2*(n+1) :=
  lt_of_le_of_lt (min_le_left _ _) ((tourNumbering p hp).symm e.out).isLt

lemma edgeFirst_orbit (a p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e) (e : Orbit a) :
    orbit a ((p^edgeFirst a p hp e) 0)=e := by
  have hr (d : Dart n) : (p^((tourNumbering p hp).symm d).val) 0=d :=
    (tourNumbering p hp).apply_symm_apply d
  unfold edgeFirst
  by_cases hh : ((tourNumbering p hp).symm e.out).val≤((tourNumbering p hp).symm (a e.out)).val
  · rw [min_eq_left hh,hr]
    exact Quotient.out_eq e
  · rw [min_eq_right (by omega),hr,orbit_perm]
    exact Quotient.out_eq e

lemma edgeFirst_injective (a p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e) :
    Function.Injective (edgeFirst a p hp) := by
  intro e f hef
  rw [← edgeFirst_orbit a p hp e,← edgeFirst_orbit a p hp f,hef]

lemma edgeFirst_le_position (a p : Perm (Dart n)) (ha : Function.Involutive a)
    (hp : ∀ d e,p.SameCycle d e) (i : Dart n) :
    edgeFirst a p hp (orbit a ((p^i.val) 0)) ≤ i.val := by
  let d := (p^i.val) 0
  have hd : orbit a d=orbit a d := rfl
  rcases (MapFinite.mk_eq_iff_involution a ha d (orbit a d)).mp hd with hh|hh
  · have hr : (tourNumbering p hp).symm (orbit a d).out=i := by
      apply (tourNumbering p hp).injective
      simpa only [Equiv.apply_symm_apply,tourNumbering_apply] using hh.symm
    exact le_trans (min_le_left _ _) (by rw [hr])
  · have hr : (tourNumbering p hp).symm (a (orbit a d).out)=i := by
      apply (tourNumbering p hp).injective
      simpa only [Equiv.apply_symm_apply,tourNumbering_apply] using hh.symm
    exact le_trans (min_le_right _ _) (by rw [hr])

/-- The adaptive tour selector is the least first occurrence in every
completed tree tour, with no choice-dependent ordering assumed. -/
theorem tourSelector_least (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R T : Finset (Orbit a)) (hR : R.Nonempty) (hC : C⊆T) (hT : T⊆C∪R)
    (ht : ∀ d e,(s*partialReversal a ha T).SameCycle d e) :
    ∀ f∈R,edgeFirst a (s*partialReversal a ha T) ht (tourSelector a s ha C R hR).val≤
      edgeFirst a (s*partialReversal a ha T) ht f := by
  obtain ⟨k,heq,hk,hbefore⟩ := tourSelector_first a s ha C R T hR hC hT ht
  have hkf (f : Orbit a) (hf : f∈R) : k≤edgeFirst a (s*partialReversal a ha T) ht f := by
    by_contra hh
    exact hbefore (edgeFirst a (s*partialReversal a ha T) ht f) (by omega) (by rw [edgeFirst_orbit]; exact hf)
  have hklt : k<2*(n+1) := by
    obtain ⟨f,hf⟩ := hR
    exact lt_of_le_of_lt (hkf f hf) (edgeFirst_lt _ _ _ f)
  intro f hf
  have hh := edgeFirst_le_position a (s*partialReversal a ha T) ha ht (⟨k,hklt⟩ : Dart n)
  simp only [heq] at hh
  exact hh.trans (hkf f hf)

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma treeExtension_next (a s : Perm (Dart n)) (C R T : Finset (Orbit a))
    (hT : T∈treeExtensions a s C R) (e : Orbit a) :
    T∈treeExtensions a s (if e∈T then insert e C else C) (R.erase e) := by
  obtain ⟨hC,hR,hf,hc⟩ := (mem_treeExtensions a s C R T).mp hT
  rw [mem_treeExtensions]
  by_cases he : e∈T
  · rw [ite_eq_left he]
    refine ⟨Finset.insert_subset_iff.mpr ⟨he,hC⟩,?_,hf,hc⟩
    intro f hf
    by_cases hfe : f=e
    · exact Finset.mem_union_left _ (hfe ▸ Finset.mem_insert_self _ _)
    · rcases Finset.mem_union.mp (hR hf) with h|h
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hfe,h⟩)
  · rw [ite_eq_right he]
    refine ⟨hC,?_,hf,hc⟩
    intro f hf
    rcases Finset.mem_union.mp (hR hf) with h|h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun hfe => he (hfe ▸ hf),h⟩)

lemma explorationActivity_step_cross (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (select : EdgeSelector a) (C R T : Finset (Orbit a)) (hR : R.Nonempty)
    (hT : T∈treeExtensions a s C R) (hd : Disjoint C R) (k : ℕ) :
    explorationActivity a s select C R T (k+1)=
      (if ∀ f∈R.erase (select C R hR).val,¬FundamentalCross a s T (select C R hR).val f then 1 else 0)+
      explorationActivity a s select (if (select C R hR).val∈T then insert (select C R hR).val C else C)
        (R.erase (select C R hR).val) T k := by
  let e := (select C R hR).val
  have heR : e∈R := (select C R hR).property
  have heC : e∉C := fun h => Finset.disjoint_left.mp hd h heR
  have ⟨hCT,hTR,hf,hc⟩ := (mem_treeExtensions a s C R T).mp hT
  by_cases he : e∈T
  · have hl : ¬(spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) := by
      intro hh
      have hf' : Multiforest a s (insert e (T.erase e)) := by rwa [Finset.insert_erase he]
      apply hf'.insert_not_reachable ha (Finset.notMem_erase _ _) (hh.mono (spanningGraph_mono a s _))
      intro f hfc
      exact Finset.mem_erase.mpr ⟨fun hfe => heC (hfe ▸ hfc),hCT hfc⟩
    have hb := treeExtension_bridge_iff_no_cross a s ha C R T hT hd he heR
    dsimp [e] at hl hb he
    simp only [explorationActivity,dite_eq_left hR]
    change (if _ then _ else if _ then _ else _)=_
    simp only [ite_eq_right hl,hb]
    simp only [he,ite_true]
    split_ifs <;> simp
  · have hb : (spanningGraph a s ((C∪R.erase e : Finset (Orbit a)) : Set (Orbit a))).Reachable
        (orbit s e.out) (orbit s (a e.out)) := by
      apply (hc.preconnected _ _).mono (spanningGraph_mono a s _)
      intro f hft
      rcases Finset.mem_union.mp (hTR hft) with hh|hh
      · exact Finset.mem_union_left _ hh
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun hfe => he (hfe ▸ hft),hh⟩)
    have hs : ¬FundamentalCross a s T e e := by simp [FundamentalCross,he]
    have hl := treeExtension_loop_iff_no_cross a s ha C R T hT hd he
    have heq : (∀ f∈R,¬FundamentalCross a s T e f) ↔
        ∀ f∈R.erase e,¬FundamentalCross a s T e f := by
      constructor
      · exact fun h f hf => h f (Finset.mem_of_mem_erase hf)
      · intro h f hf
        by_cases hfe : f=e
        · exact hfe ▸ hs
        · exact h f (Finset.mem_erase.mpr ⟨hfe,hf⟩)
    rw [heq] at hl
    dsimp [e] at hl hb he
    simp only [explorationActivity,dite_eq_left hR]
    change (if _ then _ else if _ then _ else _)=_
    simp only [hl]
    simp only [hb,not_true_eq_false,ite_false,he]
    split_ifs <;> simp

def OrderedActive (a s : Perm (Dart n)) (T : Finset (Orbit a))
    (rank : Orbit a→ℕ) (e : Orbit a) : Prop :=
  ∀ f,rank e<rank f → ¬FundamentalCross a s T e f

/-- Any increasing adaptive selector counts exactly the active edges of the
completed branch. This is an equality for the original forced-choice count. -/
theorem explorationActivity_eq_orderedActive (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (select : EdgeSelector a) (T : Finset (Orbit a)) (rank : Orbit a→ℕ)
    (hi : Function.Injective rank)
    (hmin : ∀ C R hR, T∈treeExtensions a s C R →
      ∀ f∈R,rank (select C R hR).val≤rank f)
    (k : ℕ) (C R : Finset (Orbit a)) (hk : R.card≤k)
    (hT : T∈treeExtensions a s C R) (hd : Disjoint C R)
    (hsuf : ∀ e∈R,∀ f,rank e<rank f → f∈R) :
    explorationActivity a s select C R T k=(R.filter (OrderedActive a s T rank)).card := by
  induction k generalizing C R with
  | zero =>
    have hR : R=∅ := Finset.card_eq_zero.mp (by omega)
    subst R
    simp [explorationActivity]
  | succ k ih =>
    by_cases hR : R.Nonempty
    · let e := (select C R hR).val
      have heR : e∈R := (select C R hR).property
      let R' := R.erase e
      let C' := if e∈T then insert e C else C
      have hmin' : ∀ f∈R,rank e≤rank f := hmin C R hR hT
      have hact : (∀ f∈R',¬FundamentalCross a s T e f) ↔ OrderedActive a s T rank e := by
        constructor
        · intro hh f hlt
          apply hh f (Finset.mem_erase.mpr ⟨fun hfe => by rw [hfe] at hlt; omega,hsuf e heR f hlt⟩)
        · intro hh f hf
          obtain ⟨hne,hfR⟩ := Finset.mem_erase.mp hf
          have hle := hmin' f hfR
          have hneq : rank e≠rank f := fun heq => hne (hi heq).symm
          exact hh f (by omega)
      have hk' : R'.card≤k := by
        have hh := Finset.card_erase_add_one heR
        dsimp [R']
        omega
      have hd' : Disjoint C' R' := by
        dsimp [C',R']
        split_ifs
        · exact Finset.disjoint_insert_left.mpr ⟨Finset.notMem_erase _ _,hd.mono_right (Finset.erase_subset _ _)⟩
        · exact hd.mono_right (Finset.erase_subset _ _)
      have hs' : ∀ g∈R',∀ f,rank g<rank f → f∈R' := by
        intro g hg f hgf
        have hgR := Finset.mem_of_mem_erase hg
        have hge := hmin' g hgR
        exact Finset.mem_erase.mpr ⟨fun hfe => by rw [hfe] at hgf; omega,hsuf g hgR f hgf⟩
      have hrec := ih C' R' hk' (treeExtension_next a s C R T hT e) hd' hs'
      rw [explorationActivity_step_cross a s ha select C R T hR hT hd k]
      change (if _ then 1 else 0)+explorationActivity a s select C' R' T k=_
      change (if ∀ f∈R',¬FundamentalCross a s T e f then 1 else 0)+_=_
      simp only [hact,hrec]
      conv_rhs => rw [← Finset.insert_erase heR]
      by_cases h : OrderedActive a s T rank e
      · rw [ite_eq_left h,Finset.filter_insert,ite_eq_left h,
          Finset.card_insert_of_notMem (by simp)]
        exact Nat.add_comm _ _
      · rw [ite_eq_right h,Finset.filter_insert,ite_eq_right h,zero_add]
    · have he : R=∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      subst R
      simp [explorationActivity]

/-- Specialization to the actual rooted-tour selector. Thus the exponent in
`loopPolynomial_tour_activity` is the exact ordered fundamental activity. -/
theorem tourActivity_eq_card (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (hT : T∈treeExtensions a s ∅ Finset.univ) :
    explorationActivity a s (tourSelector a s ha) ∅ Finset.univ T (Fintype.card (Orbit a)) =
      (Finset.univ.filter (OrderedActive a s T
        (edgeFirst a (s*partialReversal a ha T) (treeExtension_tour a s ha ∅ Finset.univ T hT)))).card := by
  apply explorationActivity_eq_orderedActive a s ha _ T _ (edgeFirst_injective _ _ _)
  · intro C R hR h f hf
    have hh := (mem_treeExtensions a s C R T).mp h
    exact tourSelector_least a s ha C R T hR hh.1 hh.2.1 _ f hf
  · simp
  · exact hT
  · simp
  · intro e he f hlt
    exact Finset.mem_univ f

end FKCRT
end

end OAI
