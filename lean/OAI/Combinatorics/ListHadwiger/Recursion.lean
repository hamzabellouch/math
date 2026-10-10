import OAI.Combinatorics.ListHadwiger.StageSeparation

namespace OAI

namespace LinearListHadwiger.Recursion
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem weaving_from_proxy_groups (G : SimpleGraph V) {a p : ℕ}
    (roots : Fin a → V) (x y : Fin p → V) (hr : Function.Injective roots)
    (he : ∀ i j, i ≠ j → Disjoint ({x i,y i} : Set V) {x j,y j})
    (C : (Fin a ⊕ Fin p) → Set V)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hCC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hroot : ∀ i j, roots j ∉ C i)
    (hx : ∀ i j, x j ∉ C i) (hy : ∀ i j, y j ∉ C i)
    (hclique : ∀ i j, i ≠ j → ∃ v ∈ C (.inl i), ∃ w ∈ C (.inl j), G.Adj v w)
    (hattachRoot : ∀ j, ∃ w ∈ C (.inl j), G.Adj (roots j) w)
    (hattachX : ∀ i, ∃ w ∈ C (.inr i), G.Adj (x i) w)
    (hattachY : ∀ i, ∃ w ∈ C (.inr i), G.Adj (y i) w) :
    Nonempty (WeavingWithin G Set.univ roots x y) := by
  classical
  let bag (j : Fin a) := insert (roots j) (C (.inl j))
  have hb (j : Fin a) : (G.induce (bag j)).Connected := by
    obtain ⟨w,hw,hew⟩ := hattachRoot j
    exact Incidence.connected_insert (hC (.inl j)) hw hew
  have hbd (i j : Fin a) (hij : i ≠ j) : Disjoint (bag i) (bag j) := by
    apply Set.disjoint_left.mpr
    intro v hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact hij (hr (hi.symm.trans hj))
    · exact hroot (.inl j) i (hi ▸ hj)
    · exact hroot (.inl i) j (hj ▸ hi)
    · exact Set.disjoint_left.mp (hCC (.inl i) (.inl j) (by simpa using hij)) hi hj
  let M : RootedCliqueModel G roots :=
    { branch := bag
      connected := hb
      disjoint := hbd
      adjacent := fun i j hij => by
        obtain ⟨v,hv,w,hw,hvw⟩ := hclique i j hij
        exact ⟨v,Or.inr hv,w,Or.inr hw,hvw⟩
      root_mem := fun _ => Or.inl rfl }
  let S (i : Fin p) := insert (x i) (insert (y i) (C (.inr i)))
  have hS (i : Fin p) : (G.induce (S i)).Connected := by
    obtain ⟨w,hw,hew⟩ := hattachY i
    have hh := Incidence.connected_insert (hC (.inr i)) hw hew
    obtain ⟨w,hw,hew⟩ := hattachX i
    exact Incidence.connected_insert hh (Or.inr hw) hew
  have hpaths : ∀ i, ∃ Q : G.Path (x i) (y i), ∀ v ∈ Q.val.support, v ∈ S i :=
    fun i => Assembly.path_in_connected (hS i) (Or.inl rfl) (Or.inr (Or.inl rfl))
  choose Q hQ using hpaths
  refine ⟨⟨M,fun _ _ _ => Set.mem_univ _,Q,fun _ _ _ => Set.mem_univ _,?_,?_⟩⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hi hj
    have hi' := hQ i v hi
    have hj' := hQ j v hj
    have hterm : ∀ i k, ∀ v ∈ ({x i,y i} : Set V), v ∉ C k := by
      intro i k v hv
      rcases hv with rfl | hv
      · exact hx k i
      · exact hv ▸ hy k i
    have hsplit : ∀ i v, v ∈ S i → v ∈ ({x i,y i} : Set V) ∨ v ∈ C (.inr i) := by
      intro i v hv
      rcases hv with hv | hv | hv
      · exact Or.inl (Or.inl hv)
      · exact Or.inl (Or.inr hv)
      · exact Or.inr hv
    rcases hsplit i v hi' with hi' | hi' <;> rcases hsplit j v hj' with hj' | hj'
    · exact Set.disjoint_left.mp (he i j hij) hi' hj'
    · exact hterm i (.inr j) v hi' hj'
    · exact hterm j (.inr i) v hj' hi'
    · exact Set.disjoint_left.mp (hCC (.inr i) (.inr j) (by simpa using hij)) hi' hj'
  · intro i j v hv hbag
    have hs := hQ i v hv
    change v ∈ insert (roots j) (C (.inl j)) at hbag
    rcases hs with hs | hs | hs
    · subst v
      rcases hbag with hb | hb
      · exact ⟨⟨j,hb.symm⟩,Or.inl rfl⟩
      · exact (hx (.inl j) i hb).elim
    · subst v
      rcases hbag with hb | hb
      · exact ⟨⟨j,hb.symm⟩,Or.inr rfl⟩
      · exact (hy (.inl j) i hb).elim
    · rcases hbag with hb | hb
      · exact (hroot (.inr i) j (hb ▸ hs)).elim
      · exact (Set.disjoint_left.mp (hCC (.inr i) (.inl j) (by simp)) hs hb).elim

lemma distinct_proxies {O : Type} [Fintype O]
    (G : SimpleGraph V) [DecidableRel G.Adj] (port : O → V) (Z : Finset V)
    {k : ℕ} (hc : KConnectedOn G univ k) (hk : Fintype.card O+Z.card≤k) :
    ∃ nbr : O → V, Function.Injective nbr ∧ ∀ o, nbr o ∉ Z ∧ G.Adj (port o) (nbr o) := by
  classical
  have hn (o : O) : Fintype.card O ≤ ((univ\Z).filter (G.Adj (port o))).card := by
    have hdeg := Knitting.min_degree G hc (mem_univ (port o))
    have he : Density.neighbors G univ (port o) \ Z = (univ\Z).filter (G.Adj (port o)) := by
      ext v
      simp only [Density.neighbors,mem_sdiff,mem_filter,mem_univ,true_and]
      tauto
    have hh := card_le_card (show Density.neighbors G univ (port o) ⊆
      Density.neighbors G univ (port o) \ Z ∪ Z from fun v hv => by
        by_cases hZ : v∈Z
        · exact mem_union_right _ hZ
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hv,hZ⟩))
    have hu := card_union_le (Density.neighbors G univ (port o) \ Z) Z
    rw [he] at hh hu
    omega
  obtain ⟨nbr,hi,hn'⟩ := Assembly.attach_ports (G:=G) port (univ\Z) hn
  exact ⟨nbr,hi,fun o => ⟨(mem_sdiff.mp (hn' o).1).2,(hn' o).2⟩⟩

omit [Fintype V] [DecidableEq V] in

lemma proxy_groups_of_model (G : SimpleGraph V) {a p : ℕ}
    (proxy : Fin a ⊕ (Fin p × Bool) → V)
    (M : RootedCliqueModel G proxy) :
    ∃ C : (Fin a ⊕ Fin p) → Set V,
      (∀ i, (G.induce (C i)).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (∀ j, C (.inl j)=M.branch (.inl j)) ∧
      (∀ i, proxy (.inr (i,false))∈C (.inr i) ∧ proxy (.inr (i,true))∈C (.inr i)) ∧
      (∀ i v, v∈C i → ∃ o, v∈M.branch o) := by
  classical
  let C : (Fin a ⊕ Fin p) → Set V := Sum.elim (fun j => M.branch (.inl j))
    (fun i => M.branch (.inr (i,false)) ∪ M.branch (.inr (i,true)))
  have hs (i) (v) (hv : v∈C i) : ∃ o, v∈M.branch o ∧
      (Sum.map id (fun z : Fin p × Bool => z.1) o : Fin a ⊕ Fin p) = i := by
    cases i with
    | inl j => exact ⟨.inl j,hv,rfl⟩
    | inr j =>
      rcases hv with hv|hv
      · exact ⟨.inr (j,false),hv,rfl⟩
      · exact ⟨.inr (j,true),hv,rfl⟩
  refine ⟨C,?_,?_,fun _ => rfl,fun i => ⟨Or.inl (M.root_mem _),Or.inr (M.root_mem _)⟩,?_⟩
  · intro i
    cases i with
    | inl j => exact M.connected (.inl j)
    | inr j =>
      obtain ⟨v,hv,w,hw,he⟩ := M.adjacent (.inr (j,false)) (.inr (j,true)) (by simp)
      exact SimpleGraph.connected_induce_union (M.connected _).preconnected
        (M.connected _).preconnected hv hw he
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hi hj
    obtain ⟨o,ho,hoi⟩ := hs i v hi
    obtain ⟨o',ho',hoj⟩ := hs j v hj
    exact Set.disjoint_left.mp (M.disjoint o o' (fun h => hij (hoi.symm.trans (h ▸ hoj)))) ho ho'
  · intro i v hv
    obtain ⟨o,ho,_⟩ := hs i v hv
    exact ⟨o,ho⟩

omit [Fintype V] [DecidableEq V] in
lemma connected_pullback (G : SimpleGraph V) (S B : Set V) (hBS : B⊆S)
    (hc : (G.induce B).Connected) :
    ((G.induce S).induce {v | v.val∈B}).Connected := by
  let f : G.induce B →g (G.induce S).induce {v | v.val∈B} :=
    ⟨fun v => ⟨⟨v.val,hBS v.property⟩,v.property⟩,fun h => h⟩
  refine { preconnected := ?_, nonempty := ?_ }
  · intro u v
    exact (hc.preconnected ⟨u.val.val,u.property⟩ ⟨v.val.val,v.property⟩).map f
  · obtain ⟨v⟩ := hc.nonempty
    exact ⟨f v⟩

lemma hadwiger_delete (G : SimpleGraph V) (Z : Finset V) :
    hadwigerNumber G ≤ hadwigerNumber (G.induce (↑(univ\Z):Set V))+Z.card := by
  classical
  obtain ⟨B,hB,hBB,hE⟩ := hasCliqueMinor_hadwigerNumber G
  let E := univ.filter (fun i => Disjoint (↑Z:Set V) (B i))
  have hn := eligible_bags_card Z B hBB
  change Fintype.card (Fin (hadwigerNumber G))≤E.card+Z.card at hn
  rw [Fintype.card_fin] at hn
  let e : Fin E.card ≃ E := by simpa only [Fintype.card_coe] using (Fintype.equivFin E).symm
  have hBS (i : E) : B i.val ⊆ (↑(univ\Z):Set V) := by
    intro v hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun hz => Set.disjoint_left.mp (mem_filter.mp i.property).2 hz hv⟩
  have hm : HasCliqueMinor (G.induce (↑(univ\Z):Set V)) E.card := by
    refine ⟨fun i => {v | v.val∈B (e i).val},?_,?_,?_⟩
    · intro i
      exact connected_pullback G _ _ (hBS (e i)) (hB (e i).val)
    · intro i j hij
      apply Set.disjoint_left.mpr
      intro v hi hj
      exact Set.disjoint_left.mp (hBB _ _ (fun h => hij (e.injective (Subtype.ext h)))) hi hj
    · intro i j hij
      obtain ⟨v,hv,w,hw,he⟩ := hE _ _ (fun h => hij (e.injective (Subtype.ext h)))
      exact ⟨⟨v,hBS (e i) hv⟩,hv,⟨w,hBS (e j) hw⟩,hw,he⟩
  exact hn.trans (Nat.add_le_add_right (cliqueMinor_le_hadwigerNumber hm) _)

lemma rooting_on {I : Type} [Fintype I] (G : SimpleGraph V) (S : Finset V)
    (r : I → V) (hi : Function.Injective r) (hr : ∀ i, r i∈S)
    (hc : KConnectedOn G S (2*Fintype.card I))
    (hh : 4*Fintype.card I≤hadwigerNumber (G.induce (↑S:Set V))) :
    ∃ M : RootedCliqueModel G r, ∀ i, M.branch i⊆(↑S:Set V) := by
  classical
  let rr : I → (↑S:Set V) := fun i => ⟨r i,hr i⟩
  have hir : Function.Injective rr := fun i j he => hi (congrArg Subtype.val he)
  let A := univ.image rr
  have hac : A.card=Fintype.card I := by simp [A,card_image_of_injective _ hir]
  have har (i) : rr i∈A := mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have hci : KConnectedOn (G.induce (↑S:Set V)) univ (2*A.card) := by
    rw [hac]
    exact Knitting.induce_connected G S hc
  have hhi : 4*A.card≤hadwigerNumber (G.induce (↑S:Set V)) := by simpa only [hac] using hh
  obtain ⟨M⟩ := rooting (G.induce (↑S:Set V)) A hci hhi
  let f : I → A := fun i => ⟨rr i,har i⟩
  have hif : Function.Injective f := fun _ _ he => hir (congrArg Subtype.val he)
  let N := M.reindex f hif
  let D := Knitting.model_induce G S
  let B (i : I) := D.expand (N.branch i)
  have hB (i) : B i⊆(↑S:Set V) := by
    rintro v ⟨w,_,hw⟩
    have he : v=w.val := hw
    exact he ▸ w.property
  refine ⟨⟨B,fun i => D.expand_connected (N.connected i),
    fun i j hij => D.expand_disjoint (N.disjoint i j hij),?_,?_⟩,hB⟩
  · intro i j hij
    obtain ⟨v,hv,w,hw,he⟩ := N.adjacent i j hij
    exact ⟨v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,he⟩
  · intro i
    exact ⟨rr i,N.root_mem i,rfl⟩

theorem large_minor_woven (G : SimpleGraph V) [DecidableRel G.Adj]
    {a : ℕ} (ha : 1≤a) (hc : KConnectedOn G univ (100*a))
    (hh : 64*a≤hadwigerNumber G) : Woven G a (3*a) := by
  classical
  intro roots hr _ p hp x y _ hxy
  let O := Fin a ⊕ (Fin p × Bool)
  let port : O → V := Sum.elim roots (fun z => if z.2 then y z.1 else x z.1)
  let Z := univ.image port
  have hO : Fintype.card O=a+2*p := by simp [O]; omega
  have hZ : Z.card≤a+2*p := by
    calc Z.card≤Fintype.card O := (card_image_le).trans (by simp)
         _ = a+2*p := hO
  obtain ⟨proxy,hproxy,hadj⟩ := distinct_proxies G port Z hc
    (show Fintype.card O+Z.card≤100*a by rw [hO]; omega)
  let R := univ\Z
  have hrp (o) : proxy o∈R := mem_sdiff.mpr ⟨mem_univ _,(hadj o).1⟩
  have hcR : KConnectedOn G R (2*Fintype.card O) := by
    have hd := Knitting.delete_connected G hc (subset_univ Z)
      (show Z.card<100*a by omega)
    exact Knitting.kConnected_mono hd (by rw [hO]; omega)
  have hhR : 4*Fintype.card O≤hadwigerNumber (G.induce (↑R:Set V)) := by
    have hd := hadwiger_delete G Z
    change hadwigerNumber G≤hadwigerNumber (G.induce (↑R:Set V))+Z.card at hd
    rw [hO]
    omega
  obtain ⟨M,hMR⟩ := rooting_on G R proxy hproxy hrp hcR hhR
  obtain ⟨C,hC,hCC,hCr,hCp,hCM⟩ := proxy_groups_of_model G proxy M
  have hCZ (i v) (hv : v∈C i) : v∉Z := by
    obtain ⟨o,ho⟩ := hCM i v hv
    exact (mem_sdiff.mp (hMR o ho)).2
  have hpZ (o : O) : port o∈Z := mem_image.mpr ⟨o,mem_univ _,rfl⟩
  have hrZ (j) : roots j∈Z := hpZ (.inl j)
  have hxZ (i) : x i∈Z := hpZ (.inr (i,false))
  have hyZ (i) : y i∈Z := hpZ (.inr (i,true))
  apply weaving_from_proxy_groups G roots x y hr hxy C hC hCC
    (fun i j hv => hCZ i _ hv (hrZ j))
    (fun i j hv => hCZ i _ hv (hxZ j))
    (fun i j hv => hCZ i _ hv (hyZ j))
  · intro i j hij
    rw [hCr i,hCr j]
    exact M.adjacent (.inl i) (.inl j) (fun he => hij (Sum.inl.inj he))
  · intro j
    refine ⟨proxy (.inl j),?_,(hadj (.inl j)).2⟩
    rw [hCr j]
    exact M.root_mem (.inl j)
  · intro i
    exact ⟨proxy (.inr (i,false)),(hCp i).1,(hadj (.inr (i,false))).2⟩
  · intro i
    exact ⟨proxy (.inr (i,true)),(hCp i).2,(hadj (.inr (i,true))).2⟩

end LinearListHadwiger.Recursion

end OAI
