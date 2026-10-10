import OAI.Combinatorics.ParityLifts.SetPrograms

namespace OAI

namespace ParityWL.Complexity

abbrev FlowerRecord (α : Type) := List α × ClauseList α

noncomputable def GoodFlower {α : Type} [DecidableEq α] (F : ClauseList α)
    (p q h : ℕ) (z : FlowerRecord α) : Prop :=
  z.1.toFinset.card=p ∧ (listCNF z.2).card=h ∧
    (∀ P∈z.2, P.toFinset.card=q) ∧
    (∀ P∈z.2, Disjoint z.1.toFinset P.toFinset) ∧
    (∀ P∈z.2, ∀ Q∈z.2, P.toFinset=Q.toFinset ∨ Disjoint P.toFinset Q.toFinset) ∧
    ∀ P∈z.2, z.1.toFinset ∪ P.toFinset∈listCNF F

noncomputable def GoodFlower.toFlower {α : Type} [DecidableEq α] {F : ClauseList α}
    {p q h : ℕ} {z : FlowerRecord α} (hz : GoodFlower F p q h z) :
    Sparsification.Flower (listCNF F) p q h where
  core := z.1.toFinset
  petals := listCNF z.2
  core_card := hz.1
  petals_card := hz.2.1
  petal_card := by
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := mem_listCNF.mp hP
    exact hz.2.2.1 Q hQ
  apart := by
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := mem_listCNF.mp hP
    exact hz.2.2.2.1 Q hQ
  pairwise := by
    intro P hP R hR hne
    obtain ⟨Q,hQ,rfl⟩ := mem_listCNF.mp hP
    obtain ⟨S,hS,rfl⟩ := mem_listCNF.mp hR
    exact (hz.2.2.2.2.1 Q hQ S hS).resolve_left hne
  cover := by
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := mem_listCNF.mp hP
    exact hz.2.2.2.2.2 Q hQ

lemma GoodFlower.ofFlower {α : Type} [DecidableEq α] {F : ClauseList α}
    {p q h : ℕ} {z : FlowerRecord α} (f : Sparsification.Flower (listCNF F) p q h)
    (hc : z.1.toFinset=f.core) (hp : listCNF z.2=f.petals) : GoodFlower F p q h z := by
  have hm (P : List α) (hP : P∈z.2) : P.toFinset∈f.petals := by
    rw [← hp]
    exact mem_listCNF.mpr ⟨P,hP,rfl⟩
  refine ⟨by rw [hc,f.core_card],by rw [hp,f.petals_card],?_,?_,?_,?_⟩
  · intro P hP; exact f.petal_card _ (hm P hP)
  · intro P hP; rw [hc]; exact f.apart _ (hm P hP)
  · intro P hP Q hQ
    by_cases he : P.toFinset=Q.toFinset
    · exact Or.inl he
    · exact Or.inr (f.pairwise (hm P hP) (hm Q hQ) he)
  · intro P hP; rw [hc]; exact f.cover _ (hm P hP)

noncomputable def flowerCandidates {α : Type} [DecidableEq α]
    (F : ClauseList α) (p h : ℕ) : List (FlowerRecord α) :=
  (allTuples p F.flatten).flatMap (fun C => (allTuples h F).map (fun As =>
    (C, As.map (fun A => clauseDiff A C))))

lemma mem_flowerCandidates {α : Type} [DecidableEq α] (F : ClauseList α) (p h : ℕ)
    (z : FlowerRecord α) : z∈flowerCandidates F p h ↔
      ∃ C As, C.length=p ∧ C⊆F.flatten ∧ As.length=h ∧ As⊆F ∧
        z=(C,As.map (fun A => clauseDiff A C)) := by
  simp only [flowerCandidates,List.mem_flatMap,List.mem_map,mem_allTuples]
  constructor
  · rintro ⟨C,⟨hC,hCF⟩,As,⟨hAs,hAF⟩,he⟩
    exact ⟨C,As,hC,hCF,hAs,hAF,he.symm⟩
  · rintro ⟨C,As,hC,hCF,hAs,hAF,rfl⟩
    exact ⟨C,⟨hC,hCF⟩,As,⟨hAs,hAF⟩,rfl⟩

lemma flowerCandidates_complete {α : Type} [DecidableEq α] {F : ClauseList α}
    {p q h : ℕ} (hh : 0<h) (f : Sparsification.Flower (listCNF F) p q h) :
    ∃ z∈flowerCandidates F p h, GoodFlower F p q h z := by
  classical
  have available (P : Finset α) (hP : P∈f.petals) : ∃ A∈F, A.toFinset=f.core∪P :=
    mem_listCNF.mp (f.cover P hP)
  choose rep hrep hset using available
  let C := f.core.toList
  let Ps := f.petals.attach.toList
  let As := Ps.map (fun P => rep P.1 P.2)
  let Bs := As.map (fun A => clauseDiff A C)
  have hC : C.toFinset=f.core := Finset.toList_toFinset _
  have hBset (P : {P // P∈f.petals}) :
      (clauseDiff (rep P.1 P.2) C).toFinset=P.1 := by
    rw [clauseDiff_set,hset,hC]
    ext a
    have hdis := Finset.disjoint_left.mp (f.apart P.1 P.2)
    simp only [Finset.mem_sdiff,Finset.mem_union]
    exact ⟨fun he => he.1.resolve_left he.2,
      fun he => ⟨Or.inr he,fun ha => hdis ha he⟩⟩
  have hBs : listCNF Bs=f.petals := by
    ext P
    simp only [listCNF,Bs,As,List.map_map,List.mem_toFinset,List.mem_map,Function.comp_def,hBset]
    constructor
    · rintro ⟨Q,_,rfl⟩; exact Q.2
    · intro hP
      exact ⟨⟨P,hP⟩,by simp [Ps],rfl⟩
  have hcore : C⊆F.flatten := by
    obtain ⟨P,hP⟩ := Finset.card_pos.mp (by rw [f.petals_card]; exact hh)
    intro a ha
    apply List.mem_flatten.mpr
    exact ⟨rep P hP,hrep P hP,List.mem_toFinset.mp (by rw [hset]; exact Finset.mem_union_left _ (by simpa [C] using ha))⟩
  have hAs : As⊆F := by
    intro A hA
    obtain ⟨P,_,rfl⟩ := List.mem_map.mp hA
    exact hrep P.1 P.2
  refine ⟨(C,Bs),(mem_flowerCandidates F p h _).mpr ⟨C,As,?_,hcore,?_,hAs,rfl⟩,?_⟩
  · simpa [C] using f.core_card
  · simpa [As,Ps] using f.petals_card
  · exact GoodFlower.ofFlower f hC hBs

noncomputable def flowerList {α : Type} [DecidableEq α] (F : ClauseList α) (p q h : ℕ) :
    List (FlowerRecord α) := by
  classical
  exact (flowerCandidates F p h).filter (fun z => decide (GoodFlower F p q h z))

lemma mem_flowerList {α : Type} [DecidableEq α] (F : ClauseList α) (p q h : ℕ) (z : FlowerRecord α) :
    z∈flowerList F p q h ↔ z∈flowerCandidates F p h ∧ GoodFlower F p q h z := by
  classical
  simp [flowerList]

lemma flowerList_ne_nil {α : Type} [DecidableEq α] (F : ClauseList α) (p q h : ℕ) (hh : 0<h) :
    flowerList F p q h≠[] ↔ Nonempty (Sparsification.Flower (listCNF F) p q h) := by
  constructor
  · intro he
    obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _ he
    exact ⟨((mem_flowerList F p q h z).mp hz).2.toFlower⟩
  · rintro ⟨f⟩ he
    obtain ⟨z,hz,hg⟩ := flowerCandidates_complete hh f
    have : z∈flowerList F p q h := (mem_flowerList F p q h z).mpr ⟨hz,hg⟩
    simp [he] at this

noncomputable def selectedFlower {α : Type} [DecidableEq α] (F : ClauseList α) (p q h : ℕ) : FlowerRecord α :=
  (flowerList F p q h).headD ([],[])

lemma selectedFlower_good {α : Type} [DecidableEq α] (F : ClauseList α) (p q h : ℕ)
    (he : flowerList F p q h≠[]) : GoodFlower F p q h (selectedFlower F p q h) :=
  ((mem_flowerList F p q h _).mp (by
    unfold selectedFlower
    cases heq : flowerList F p q h with
    | nil => exact (he heq).elim
    | cons a as => simp)).2

end ParityWL.Complexity

end OAI
