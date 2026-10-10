import OAI.Combinatorics.ListHadwiger.District

namespace OAI

namespace LinearListHadwiger.District
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma list_dense_core (G : SimpleGraph V) {d : ℕ}
    (hl : d+1 < listChromaticNumber G) :
    ∃ S : Finset V, S.Nonempty ∧
      (d+1)*S.card ≤ 2*(G.induce (↑S:Set V)).edgeFinset.card := by
  classical
  have hnot : ¬DegenerateOn G univ d := by
    intro h
    exact (not_le_of_gt hl) (listChromaticNumber_le_of_degenerate G h)
  have hx : ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, d < (S.filter (G.Adj v)).card := by
    by_contra hn
    apply hnot
    intro S _ hS
    by_contra hh
    apply hn
    refine ⟨S,hS,?_⟩
    intro v hv
    by_contra hn
    exact hh ⟨v,hv,by omega⟩
  obtain ⟨S,hS,hdeg⟩ := hx
  refine ⟨S,hS,?_⟩
  rw [←darts_induce,darts_sum]
  calc
    (d+1)*S.card = ∑ v ∈ S, (d+1) := by simp [mul_comm]
    _ ≤ _ := sum_le_sum fun v hv => by have := hdeg v hv; omega

theorem list_district : ∀ K : ℕ, 0 < K → ∃ D : ℕ,
    max (400*3202) (12800*K) < D ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (P : SimpleGraph W),
    hadwigerNumber P < t → 2*D*t+2 < listChromaticNumber P →
    ∃ S : Finset W, KConnectedOn P S (K*t) ∧
      (S.card : ℝ) ≤ (t:ℝ)^(53/50:ℝ) := by
  intro K hK
  obtain ⟨D,hD,t₀,hd⟩ := district K hK
  refine ⟨D,hD,t₀,?_⟩
  intro t ht W _ _ P hex hl
  obtain ⟨A,hA,hden⟩ := list_dense_core P (d := 2*D*t+1) (by omega)
  let : Nonempty (↑A:Set W) := ⟨⟨hA.choose,hA.choose_spec⟩⟩
  have hh := (Knitting.model_induce P A).hadwiger_le.trans_lt hex
  have he : D*t*Fintype.card (↑A:Set W) ≤ (P.induce (↑A:Set W)).edgeFinset.card := by
    have hAc : Fintype.card (↑A:Set W) = A.card := by simp
    rw [hAc]
    nlinarith
  obtain ⟨S,hSc,hcard⟩ := hd t ht (↑A:Set W) (P.induce (↑A:Set W)) hh he
  refine ⟨S.image Subtype.val,kConnected_image Subtype.val Subtype.val_injective hSc
    (fun _ _ _ _ h => h),?_⟩
  simpa only [card_image_of_injective _ Subtype.val_injective] using hcard

end
end LinearListHadwiger.District

namespace LinearListHadwiger.Assembly
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V O : Type} [Fintype V] [DecidableEq V] [Fintype O] [DecidableEq O]

theorem clique_from_private_occurrences {V O : Type} [Fintype V] [DecidableEq V] [Fintype O] [DecidableEq O] (G : SimpleGraph V) {t : ℕ}
    (label : O → Fin t) (hs : Function.Surjective label) (hO : 1 ≤ Fintype.card O)
    (B : O → Set V) (U : Finset V)
    (hB : ∀ o, (G.induce (B o)).Connected)
    (hBB : ∀ o p, label o ≠ label p → Disjoint (B o) (B p))
    (hU : ∀ o, Disjoint (B o) (↑U : Set V))
    (hN : ∀ o, ∀ v ∈ B o, Fintype.card O ≤ (U.filter (G.Adj v)).card)
    (hconn : KConnectedOn G U (65536 * Fintype.card O))
    (hpairs : ∀ i j, i ≠ j → ∃ o p, label o = i ∧ label p = j ∧
      ∃ x ∈ B o, ∃ y ∈ B p, G.Adj x y) : HasCliqueMinor G t := by
  classical
  have hp : ∀ o, ∃ v, v ∈ B o := fun o => by
    obtain ⟨v⟩ := (hB o).nonempty
    exact ⟨v.val,v.property⟩
  choose port hp using hp
  obtain ⟨nbr,hni,hn⟩ := attach_ports (G := G) port U (fun o => hN o (port o) (hp o))
  let nr : O → (↑U : Set V) := fun o => ⟨nbr o,(hn o).1⟩
  have hnr : Function.Injective nr := fun _ _ he => hni (congrArg Subtype.val he)
  let A : Finset (↑U : Set V) := univ.image nr
  have hAc : A.card = Fintype.card O := by
    rw [card_image_of_injective _ hnr,card_univ]
  have ha (o : O) : nr o ∈ A := mem_image.mpr ⟨o,mem_univ _,rfl⟩
  have hpre : ∀ a : ↥A, ∃ o, nr o = a.val := by
    intro a
    obtain ⟨o,_,ho⟩ := mem_image.mp a.property
    exact ⟨o,ho⟩
  choose idx hidx using hpre
  have hi (o : O) : idx ⟨nr o,ha o⟩ = o := hnr (hidx ⟨nr o,ha o⟩)
  let lab : ↥A → Fin t := fun a => label (idx a)
  have hls : Function.Surjective lab := by
    intro i
    obtain ⟨o,rfl⟩ := hs i
    exact ⟨⟨nr o,ha o⟩,congrArg label (hi o)⟩
  have hc : KConnectedOn (G.induce (↑U : Set V)) univ (65536*A.card) := by
    rw [hAc]
    exact Knitting.induce_connected G U hconn
  obtain ⟨C,hC,hCC,hterm⟩ := Knitting.group_terminals (G.induce (↑U : Set V)) A lab hls
    (by omega) hc
  let M := Knitting.model_induce G U
  let D : Fin t → Set V := fun i => M.expand (C i)
  have hDU : ∀ i, D i ⊆ (↑U : Set V) := by
    intro i v hv
    obtain ⟨w,_,hw⟩ := hv
    have he : v = w.val := hw
    exact he ▸ w.property
  apply clique_of_occurrences (G := G) label B D hB
    (fun i => M.expand_connected (hC i)) hBB
    (fun i j hij => M.expand_disjoint (hCC i j hij))
    (fun o i => (hU o).mono_right (hDU i))
  · intro o
    refine ⟨port o,hp o,nbr o,?_,(hn o).2⟩
    refine ⟨nr o,?_,rfl⟩
    have ht := hterm ⟨nr o,ha o⟩
    simpa only [lab,hi] using ht
  · exact hpairs

theorem clique_from_private_models {Q : Type} [Fintype Q] [DecidableEq Q]
    (G : SimpleGraph V) {t a : ℕ} (ht : 1 ≤ t)
    (L : Q → Finset (Fin t)) (hL : ∀ q, (L q).card ≤ a)
    (hcover : ∀ i, ∃ q, i ∈ L q)
    (hpair : ∀ i j, i ≠ j → ∃ q, i ∈ L q ∧ j ∈ L q)
    (S : Q → Finset V) (U : Finset V)
    (hd : ∀ q r, q ≠ r → Disjoint (S q) (S r))
    (hSU : ∀ q, Disjoint (S q) U)
    (hm : ∀ q, HasCliqueMinor (G.induce (↑(S q) : Set V)) a)
    (hN : ∀ q, ∀ v ∈ S q, a*Fintype.card Q ≤ (U.filter (G.Adj v)).card)
    (hc : KConnectedOn G U (65536*(a*Fintype.card Q))) : HasCliqueMinor G t := by
  classical
  choose P hP using hm
  let M (q : Q) := Knitting.model_induce G (S q)
  let R (q : Q) (j : Fin a) : Set V := (M q).expand (P q j)
  have hRS : ∀ q j, R q j ⊆ (↑(S q) : Set V) := by
    intro q j v hv
    obtain ⟨w,_,hw⟩ := hv
    have he : v = w.val := hw
    exact he ▸ w.property
  let E (q : Q) : ↥(L q) ↪ Fin a :=
    (Fintype.equivFin ↥(L q)).toEmbedding.trans
      (Fin.castLEEmb (show Fintype.card ↥(L q) ≤ a by simpa using hL q))
  let O := Σ q : Q, ↥(L q)
  let label : O → Fin t := fun o => o.2.val
  let B : O → Set V := fun o => R o.1 (E o.1 o.2)
  have hsurj : Function.Surjective label := by
    intro i
    obtain ⟨q,hi⟩ := hcover i
    exact ⟨⟨q,⟨i,hi⟩⟩,rfl⟩
  have hbudget : Fintype.card O ≤ a*Fintype.card Q := by
    calc
      Fintype.card O = ∑ q, (L q).card := by simp [O,Fintype.card_sigma]
      _ ≤ ∑ _q : Q, a := sum_le_sum fun q _ => hL q
      _ = a*Fintype.card Q := by simp [mul_comm]
  have hO : 1 ≤ Fintype.card O := by
    have hx := Fintype.card_le_of_surjective label hsurj
    simp only [Fintype.card_fin] at hx
    omega
  apply clique_from_private_occurrences G label hsurj hO B U
  · intro o
    exact (M o.1).expand_connected ((hP o.1).1 _)
  · intro o p hop
    by_cases he : o.1 = p.1
    · obtain ⟨oq,oi⟩ := o
      obtain ⟨pq,pi⟩ := p
      dsimp at he
      subst pq
      apply (M oq).expand_disjoint
      apply (hP oq).2.1
      intro hij
      have hi := (E oq).injective hij
      exact hop (congrArg Subtype.val hi)
    · exact Set.disjoint_left.mpr (fun v hvo hvp =>
        Finset.disjoint_left.mp (hd o.1 p.1 he) (hRS _ _ hvo) (hRS _ _ hvp))
  · intro o
    exact Set.disjoint_left.mpr (fun v hv hu =>
      Finset.disjoint_left.mp (hSU o.1) (hRS _ _ hv) hu)
  · intro o v hv
    exact hbudget.trans (hN o.1 v (hRS _ _ hv))
  · exact Knitting.kConnected_mono hc (Nat.mul_le_mul_left 65536 hbudget)
  · intro i j hij
    obtain ⟨q,hi,hj⟩ := hpair i j hij
    let oi : O := ⟨q,⟨i,hi⟩⟩
    let oj : O := ⟨q,⟨j,hj⟩⟩
    have he : E q ⟨i,hi⟩ ≠ E q ⟨j,hj⟩ := fun h =>
      hij (congrArg Subtype.val ((E q).injective h))
    obtain ⟨v,hv,w,hw,hvw⟩ := (hP q).2.2 _ _ he
    exact ⟨oi,oj,rfl,rfl,v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,hvw⟩

theorem clique_from_block_models (G : SimpleGraph V) {t b x : ℕ}
    (ht : 1 ≤ t) (hx : 1 ≤ x) (htb : t ≤ b*x)
    (S : (Fin b × Fin b) → Finset V) (U : Finset V)
    (hd : ∀ q r, q ≠ r → Disjoint (S q) (S r))
    (hSU : ∀ q, Disjoint (S q) U)
    (hm : ∀ q, HasCliqueMinor (G.induce (↑(S q) : Set V)) (2*x))
    (hN : ∀ q, ∀ v ∈ S q, 2*x*b^2 ≤ (U.filter (G.Adj v)).card)
    (hc : KConnectedOn G U (65536*(2*x*b^2))) : HasCliqueMinor G t := by
  classical
  let block : Fin t → Fin b := fun i => ⟨i.val/x,(Nat.div_lt_iff_lt_mul (by omega)).mpr
    (i.isLt.trans_le htb)⟩
  let L (q : Fin b × Fin b) : Finset (Fin t) :=
    (univ.filter fun i => block i=q.1) ∪ (univ.filter fun i => block i=q.2)
  have hblock (j : Fin b) : (univ.filter fun i => block i=j).card ≤ x := by
    let A := univ.filter fun i => block i=j
    let f : ↥A → Fin x := fun i => ⟨i.val.val%x,Nat.mod_lt _ (by omega)⟩
    have hf : Function.Injective f := by
      intro i k he
      apply Subtype.ext
      apply Fin.ext
      have hid : i.val.val/x=j.val := congrArg Fin.val (mem_filter.mp i.property).2
      have hkd : k.val.val/x=j.val := congrArg Fin.val (mem_filter.mp k.property).2
      have hm : i.val.val%x=k.val.val%x := congrArg Fin.val he
      have hi := Nat.mod_add_div i.val.val x
      have hk := Nat.mod_add_div k.val.val x
      rw [hid] at hi
      rw [hkd] at hk
      omega
    have hh := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe,Fintype.card_fin] using hh
  refine clique_from_private_models G ht L (fun q => (card_union_le _ _).trans (by
    have h₁ := hblock q.1
    have h₂ := hblock q.2
    omega)) ?_ ?_ S U hd hSU hm ?_ ?_
  · intro i
    refine ⟨(block i,block i),?_⟩
    exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,rfl⟩)
  · intro i j _
    refine ⟨(block i,block j),?_,?_⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,rfl⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,rfl⟩)
  · intro q v hv
    simpa only [Fintype.card_prod,Fintype.card_fin,pow_two,mul_assoc] using hN q v hv
  · simpa only [Fintype.card_prod,Fintype.card_fin,pow_two,mul_assoc] using hc

end
end LinearListHadwiger.Assembly

end OAI
