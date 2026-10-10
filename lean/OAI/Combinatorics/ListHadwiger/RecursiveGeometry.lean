import OAI.Combinatorics.ListHadwiger.Recursion

namespace OAI

namespace LinearListHadwiger.Recursion
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V I : Type} [DecidableEq V] [Fintype I] {G : SimpleGraph V}

theorem reroute_selected (J : Set V) {a b : ℕ} (hJ : WovenOn G J a b)
    (u : Fin a → V) (hu : Function.Injective u) (huJ : ∀ j, u j∈J)
    (keep : Fin a → Prop)
    (x y : I → V) (P : ∀ i, G.Path (x i) (y i))
    (hcard : Fintype.card I ≤ b)
    (hPP : ∀ i j, i≠j → Disjoint {v | v∈(P i).val.support} {v | v∈(P j).val.support})
    (hroot : ∀ i j, keep j → u j∈(P i).val.support → u j=x i) :
    ∃ M : RootedCliqueModel G u, (∀ j, M.branch j⊆J) ∧
    ∃ Q : ∀ i, G.Path (x i) (y i),
      (∀ i j, i≠j → Disjoint {v | v∈(Q i).val.support} {v | v∈(Q j).val.support}) ∧
      (∀ i v, v∈(Q i).val.support → v∉J → v∈(P i).val.support) ∧
      (∀ i j v, keep j → v∈(Q i).val.support → v∈M.branch j → v=x i ∧ v=u j) := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  obtain ⟨M,hMJ,Q,hQQ,_,hQP,hQM⟩ := reroute_woven_district G J hJ u hu huJ
    (x ∘ e) (y ∘ e) (fun i => P (e i)) hcard
    (fun i j hij => hPP _ _ (fun h => hij (e.injective h)))
  let Q' : ∀ i, G.Path (x i) (y i) := fun i =>
    ⟨(Q (e.symm i)).val.copy (congrArg x (e.apply_symm_apply i))
      (congrArg y (e.apply_symm_apply i)),by simp⟩
  have hsup (i : I) (v : V) : v∈(Q' i).val.support ↔ v∈(Q (e.symm i)).val.support := by
    simp [Q']
  refine ⟨M,hMJ,Q',?_,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hv hw
    exact Set.disjoint_left.mp (hQQ _ _ (fun h => hij (e.symm.injective h)))
      ((hsup i v).mp hv) ((hsup j v).mp hw)
  · intro i v hv hvJ
    have he := congrArg (fun j => (P j).val.support) (e.apply_symm_apply i)
    exact he ▸ hQP _ v ((hsup i v).mp hv) hvJ
  · intro i j v hjkeep hv hvm
    obtain ⟨⟨j',rfl⟩,D,hD⟩ := hQM _ j v ((hsup i v).mp hv) hvm
    have hj : j'=j := by
      by_contra hne
      exact Set.disjoint_left.mp (M.disjoint j' j hne) (M.root_mem j') hvm
    have horig : u j'∈(P i).val.support := by
      have he := congrArg (fun j => (P j).val.support) (e.apply_symm_apply i)
      rw [←he]
      rcases hD with hd | hd
      · exact hd.symm ▸ D.entry_on
      · exact hd.symm ▸ D.exit_on
    exact ⟨hroot i j' (hj ▸ hjkeep) horig,congrArg u hj⟩

omit [DecidableEq V] [Fintype I] in
lemma source_only (x y : I → V) (P : ∀ i, G.Path (x i) (y i))
    (hPP : ∀ i j, i≠j → Disjoint {v | v∈(P i).val.support} {v | v∈(P j).val.support})
    (i j : I) (h : x j∈(P i).val.support) : x j=x i := by
  by_cases he : i=j
  · exact he ▸ rfl
  · exact (Set.disjoint_left.mp (hPP i j he) h (P j).val.start_mem_support).elim

omit [DecidableEq V] [Fintype I] in

lemma rooted_of_occurrences {O : Type} (G : SimpleGraph V) (r : I → V)
    (hr : Function.Injective r) (label : O → I) (B : O → Set V)
    (hB : ∀ o, (G.induce (B o)).Connected)
    (hBB : ∀ o p, label o≠label p → Disjoint (B o) (B p))
    (hroot : ∀ o i, r i∉B o)
    (hattach : ∀ o, ∃ v∈B o, G.Adj v (r (label o)))
    (hpairs : ∀ i j, i≠j → ∃ o p, label o=i ∧ label p=j ∧
      ∃ v∈B o, ∃ w∈B p, G.Adj v w) :
    ∃ M : RootedCliqueModel G r,
      ∀ i, M.branch i={r i}∪{v | ∃ o, label o=i ∧ v∈B o} := by
  let C (i : I) := {r i}∪{v | ∃ o, label o=i ∧ v∈B o}
  have hc (i) : (G.induce (C i)).Connected := by
    have hsingleton : (G.induce ({r i}:Set V)).Connected := by
      have : Nonempty ({r i}:Set V) := ⟨⟨r i,rfl⟩⟩
      exact Connected.of_subsingleton
    have h := Assembly.connected_glue G {r i}
      (fun o : {o // label o=i} => B o.val) hsingleton (fun o => hB o.val) (fun o => by
        obtain ⟨v,hv,he⟩ := hattach o.val
        exact ⟨v,hv,r i,rfl,by simpa only [o.property] using he⟩)
    have he : C i={r i}∪{v | ∃ o : {o // label o=i},v∈B o.val} := by
      ext v
      simp only [C,Set.mem_union,Set.mem_ofPred_eq,Subtype.exists,exists_prop]
    exact he ▸ h
  refine ⟨⟨C,hc,?_,?_,fun _ => Or.inl rfl⟩,fun _ => rfl⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hi hj
    rcases hi with hi | ⟨o,ho,hi⟩ <;> rcases hj with hj | ⟨p,hp,hj⟩
    · exact hij (hr (hi.symm.trans hj))
    · exact hroot p i (hi ▸ hj)
    · exact hroot o j (hj ▸ hi)
    · exact Set.disjoint_left.mp (hBB o p (by simpa only [ho,hp] using hij)) hi hj
  · intro i j hij
    obtain ⟨o,p,ho,hp,v,hv,w,hw,he⟩ := hpairs i j hij
    exact ⟨v,Or.inr ⟨o,ho,hv⟩,w,Or.inr ⟨p,hp,hw⟩,he⟩

theorem reroute_disjoint_districts {D : Type} [Fintype D]
    (J : D → Set V) {a b : ℕ} (hJ : ∀ d, WovenOn G (J d) a b)
    (hJJ : ∀ d e, d≠e → Disjoint (J d) (J e))
    (u : D → Fin a → V) (hu : ∀ d, Function.Injective (u d)) (huJ : ∀ d j, u d j∈J d)
    (x y : I → V) (P : ∀ i, G.Path (x i) (y i))
    (hcard : Fintype.card I≤b)
    (hPP : ∀ i j, i≠j → Disjoint {v | v∈(P i).val.support} {v | v∈(P j).val.support}) :
    ∃ M : ∀ d, RootedCliqueModel G (u d), (∀ d j, (M d).branch j⊆J d) ∧
    ∃ Q : ∀ i, G.Path (x i) (y i),
      (∀ i j, i≠j → Disjoint {v | v∈(Q i).val.support} {v | v∈(Q j).val.support}) ∧
      (∀ i v, v∈(Q i).val.support → (∀ d, v∉J d) → v∈(P i).val.support) ∧
      (∀ d i j v, (∃ k, x k=u d j) → v∈(Q i).val.support →
        v∈(M d).branch j → v=x i ∧ v=u d j) := by
  classical
  have step (S : Finset D) :
      ∃ M : ∀ d∈S, RootedCliqueModel G (u d), (∀ d hd j, (M d hd).branch j⊆J d) ∧
      ∃ Q : ∀ i, G.Path (x i) (y i),
        (∀ i j, i≠j → Disjoint {v | v∈(Q i).val.support} {v | v∈(Q j).val.support}) ∧
        (∀ i v, v∈(Q i).val.support → (∀ d, v∉J d) → v∈(P i).val.support) ∧
        (∀ d hd i j v, (∃ k, x k=u d j) → v∈(Q i).val.support →
          v∈(M d hd).branch j → v=x i ∧ v=u d j) := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨fun d hd => (notMem_empty d hd).elim,fun d hd => (notMem_empty d hd).elim,
        P,hPP,fun _ _ hv _ => hv,fun d hd => (notMem_empty d hd).elim⟩
    | @insert d S hd ih =>
      obtain ⟨M,hMJ,Q,hQQ,hQP,hQM⟩ := ih
      obtain ⟨N,hNJ,R,hRR,hRQ,hRN⟩ := reroute_selected (J d) (hJ d) (u d) (hu d) (huJ d)
        (fun j => ∃ i, x i=u d j) x y Q hcard hQQ (by
          intro i j hj hv
          obtain ⟨k,hk⟩ := hj
          rw [←hk] at hv
          exact hk.symm.trans (source_only x y Q hQQ i k hv))
      let M' : ∀ e∈insert d S, RootedCliqueModel G (u e) := fun e he =>
        if h : e=d then h.symm ▸ N else M e ((mem_insert.mp he).resolve_left h)
      have hnew (he : d∈insert d S) : M' d he=N := by simp [M']
      have hold (e : D) (he : e∈insert d S) (hne : e≠d) :
          M' e he=M e ((mem_insert.mp he).resolve_left hne) := by simp [M',hne]
      refine ⟨M',?_,R,hRR,?_,?_⟩
      · intro e he j
        by_cases h : e=d
        · subst e
          rw [hnew he]
          exact hNJ j
        · rw [hold e he h]
          exact hMJ e _ j
      · intro i v hv hvJ
        exact hQP i v (hRQ i v hv (hvJ d)) hvJ
      · intro e he i j v hj hv hvm
        by_cases h : e=d
        · subst e
          rw [hnew he] at hvm
          exact hRN i j v hj hv hvm
        · rw [hold e he h] at hvm
          have hvJ : v∉J d := fun hvd =>
            Set.disjoint_left.mp (hJJ e d h) (hMJ e _ j hvm) hvd
          exact hQM e _ i j v hj (hRQ i v hv hvJ) hvm
  obtain ⟨M,hMJ,Q,hQQ,hQP,hQM⟩ := step univ
  exact ⟨fun d => M d (mem_univ d),fun d j => hMJ d _ j,Q,hQQ,hQP,
    fun d => hQM d (mem_univ d)⟩

lemma paired_paths_on [Fintype V] [DecidableEq I]
    (G : SimpleGraph V) (S : Finset V) (z : I × Bool → V)
    (hz : Function.Injective z) (hzS : ∀ o, z o∈S)
    (hI : 1≤Fintype.card I)
    (hc : KConnectedOn G S (65536*(2*Fintype.card I))) :
    ∃ P : ∀ i, G.Path (z (i,false)) (z (i,true)),
      (∀ i v, v∈(P i).val.support → v∈S) ∧
      ∀ i j, i≠j → Disjoint {v | v∈(P i).val.support} {v | v∈(P j).val.support} := by
  have hp : 1≤Fintype.card (I × Bool) := by simp only [Fintype.card_prod,Fintype.card_bool]; omega
  have hc' : KConnectedOn G S (65536*Fintype.card (I×Bool)) := by
    simpa only [Fintype.card_prod,Fintype.card_bool,Nat.mul_comm (Fintype.card I) 2] using hc
  obtain ⟨C,hC,hCC,hCS,hzC⟩ := Stage.grouped_ends G S z hz hzS Prod.fst
    (fun i => ⟨(i,false),rfl⟩) hp hc'
  have hex (i : I) : ∃ P : G.Path (z (i,false)) (z (i,true)), ∀ v∈P.val.support, v∈C i :=
    Assembly.path_in_connected (hC i) (hzC (i,false)) (hzC (i,true))
  choose P hP using hex
  refine ⟨P,fun i v hv => hCS i (hP i v hv),?_⟩
  intro i j hij
  exact Set.disjoint_left.mpr (fun v hi hj => Set.disjoint_left.mp (hCC i j hij) (hP i v hi) (hP j v hj))

omit [DecidableEq V] [Fintype I] in

lemma rooted_from_bag_routes {O : Type} (G : SimpleGraph V)
    (r : I → V) (hr : Function.Injective r) (label : O → I)
    (x y : O → V) (hx : Function.Injective x)
    (C : O → Set V) (P : ∀ o, G.Path (x o) (y o))
    (hC : ∀ o, (G.induce (C o)).Connected) (hCx : ∀ o, x o∈C o)
    (hCC : ∀ o p, o≠p → Disjoint (C o) (C p))
    (hPP : ∀ o p, o≠p → Disjoint {v | v∈(P o).val.support} {v | v∈(P p).val.support})
    (hPC : ∀ o p v, v∈(P o).val.support → v∈C p → v=x o ∧ v=x p)
    (hRC : ∀ o i, r i∉C o)
    (hRP : ∀ o i, r i∉(P o).val.support)
    (hadj : ∀ o, G.Adj (y o) (r (label o)))
    (hpairs : ∀ i j, i≠j → ∃ o p, label o=i ∧ label p=j ∧
      ∃ v∈C o, ∃ w∈C p, G.Adj v w) :
    ∃ M : RootedCliqueModel G r, ∀ i,
      M.branch i={r i}∪{v | ∃ o, label o=i ∧ (v∈C o ∨ v∈(P o).val.support)} := by
  let B (o : O) := C o∪{v | v∈(P o).val.support}
  have hB (o) : (G.induce (B o)).Connected :=
    Stage.attached_connected C x y P hC hCx o
  have hBB (o p) (hop : label o≠label p) : Disjoint (B o) (B p) := by
    have hne : o≠p := fun h => hop (congrArg label h)
    apply Set.disjoint_left.mpr
    intro v ho hp
    rcases ho with ho|ho <;> rcases hp with hp|hp
    · exact Set.disjoint_left.mp (hCC o p hne) ho hp
    · have he := hPC p o v hp ho
      exact hne (hx (he.2.symm.trans he.1))
    · have he := hPC o p v ho hp
      exact hne (hx (he.1.symm.trans he.2))
    · exact Set.disjoint_left.mp (hPP o p hne) ho hp
  apply rooted_of_occurrences G r hr label B hB hBB
  · intro o i hi
    exact hi.elim (hRC o i) (hRP o i)
  · intro o
    exact ⟨y o,Or.inr (P o).val.end_mem_support,hadj o⟩
  · intro i j hij
    obtain ⟨o,p,ho,hp,v,hv,w,hw,he⟩ := hpairs i j hij
    exact ⟨o,p,ho,hp,v,Or.inl hv,w,Or.inl hw,he⟩

end LinearListHadwiger.Recursion

end OAI
