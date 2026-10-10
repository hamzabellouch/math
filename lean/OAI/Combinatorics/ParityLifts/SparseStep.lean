import OAI.Combinatorics.ParityLifts.FlowerPrograms

namespace OAI

namespace Sparsification

variable {α : Type} [DecidableEq α] [Fintype α] {r : ℕ}

lemma split_from_two (hr : 0<r) (s : State α (r^2)) (f : Flower s.formula 1 1 (r^2)) :
    ∃ sp : Split s, sp.left.formula=prune s.formula {f.core} ∧ sp.right.formula=prune s.formula f.petals := by
  have hr2 : 0<r^2 := pow_pos hr _
  have hr4 : 0<r^4 := pow_pos hr _
  have hc : ∀ C∈({f.core}:CNF α), C.card=1 := by
    intro C hC; obtain rfl := Finset.mem_singleton.mp hC; exact f.core_card
  let l := s.addUnits {f.core} hc (f.core_fresh s.reduced (by omega) hr2)
  let t := s.addUnits f.petals f.petal_card (f.petals_fresh s.reduced (by omega))
  refine ⟨⟨l,t,r^2,r^4,hr2,hr4,?_,?_,split_units hr,f.branch_holds⟩,rfl,rfl⟩
  · simpa [l] using s.spent_addUnits {f.core} hc (f.core_fresh s.reduced (by omega) hr2)
  · have he : r^2*r^2=r^4 := by ring
    simpa [t, f.petals_card,he] using s.spent_addUnits f.petals f.petal_card (f.petals_fresh s.reduced (by omega))

lemma split_from_three_binary (hr : 0<r) (s : State α (r^2))
    (hn : ¬Nonempty (Flower s.formula 1 1 (r^2))) (f : Flower s.formula 2 1 (r^4)) :
    ∃ sp : Split s, sp.left.formula=prune s.formula {f.core} ∧ sp.right.formula=prune s.formula f.petals := by
  have hr4 : 0<r^4 := pow_pos hr _
  have hc : ∀ C∈({f.core}:CNF α), C.card=2 := by
    intro C hC; obtain rfl := Finset.mem_singleton.mp hC; exact f.core_card
  let l := s.addBinaries {f.core} hc (f.core_fresh s.reduced (by omega) hr4)
    (singleton_degree_le_one f.core) hn
  let t := s.addUnits f.petals f.petal_card (f.petals_fresh s.reduced (by omega))
  refine ⟨⟨l,t,1,r^6,by omega,pow_pos hr _,?_,?_,split_binary hr,f.branch_holds⟩,rfl,rfl⟩
  · exact s.spent_addBinaries {f.core} hc (f.core_fresh s.reduced (by omega) hr4) (singleton_degree_le_one f.core) hn
  · have he : r^2*r^4=r^6 := by ring
    simpa [t,f.petals_card,he] using s.spent_addUnits f.petals f.petal_card (f.petals_fresh s.reduced (by omega))

lemma split_from_three_unit (hr : 0<r) (s : State α (r^2))
    (hn : ¬Nonempty (Flower s.formula 1 1 (r^2))) (f : Flower s.formula 1 2 (r^4)) :
    ∃ sp : Split s, sp.left.formula=prune s.formula {f.core} ∧ sp.right.formula=prune s.formula f.petals := by
  have hr2 : 0<r^2 := pow_pos hr _
  have hr4 : 0<r^4 := pow_pos hr _
  have hc : ∀ C∈({f.core}:CNF α), C.card=1 := by
    intro C hC; obtain rfl := Finset.mem_singleton.mp hC; exact f.core_card
  let l := s.addUnits {f.core} hc (f.core_fresh s.reduced (by omega) hr4)
  let t := s.addBinaries f.petals f.petal_card (f.petals_fresh s.reduced (by omega))
    (pairwise_degree_le_one f.petals f.pairwise) hn
  refine ⟨⟨l,t,r^2,r^4,hr2,hr4,?_,?_,split_units hr,f.branch_holds⟩,rfl,rfl⟩
  · simpa [l] using s.spent_addUnits {f.core} hc (f.core_fresh s.reduced (by omega) hr4)
  · simpa [t,f.petals_card] using s.spent_addBinaries f.petals f.petal_card
      (f.petals_fresh s.reduced (by omega)) (pairwise_degree_le_one f.petals f.pairwise) hn

end Sparsification

namespace ParityWL.Complexity

abbrev SparseResult (α : Type) := Bool × ClauseList α × ClauseList α

noncomputable def sparseBranch {α : Type} [DecidableEq α] (F : ClauseList α) (z : FlowerRecord α) : SparseResult α :=
  (false,pruneList F [z.1],pruneList F z.2)

noncomputable def sparseStep {α : Type} [DecidableEq α] (r : ℕ) (F : ClauseList α) : SparseResult α :=
  if (flowerList F 1 1 (r^2)).isEmpty then
    if (flowerList F 2 1 (r^4)).isEmpty then
      if (flowerList F 1 2 (r^4)).isEmpty then (true,F,F)
      else sparseBranch F (selectedFlower F 1 2 (r^4))
    else sparseBranch F (selectedFlower F 2 1 (r^4))
  else sparseBranch F (selectedFlower F 1 1 (r^2))

lemma sparseStep_spec {α : Type} [DecidableEq α] [Fintype α] {r : ℕ} (hr : 0<r)
    (s : Sparsification.State α (r^2)) (F : ClauseList α) (he : listCNF F=s.formula) :
    ((sparseStep r F).1=true ∧ (sparseStep r F).2.1=F ∧ (sparseStep r F).2.2=F ∧ Sparsification.Terminal s.formula r) ∨
    ((sparseStep r F).1=false ∧ ∃ sp : Sparsification.Split s,
      listCNF (sparseStep r F).2.1=sp.left.formula ∧ listCNF (sparseStep r F).2.2=sp.right.formula) := by
  classical
  have hterm (p q h : ℕ) (hh : 0<h) (h0 : (flowerList F p q h).isEmpty=true) :
      ¬Nonempty (Sparsification.Flower s.formula p q h) := by
    rw [← he,← flowerList_ne_nil F p q h hh]
    simpa using congrArg (fun b => b=true) h0
  have branch (p q h : ℕ) (hx : (flowerList F p q h).isEmpty≠true)
      (hs : ∀ f : Sparsification.Flower s.formula p q h,
        ∃ sp : Sparsification.Split s, sp.left.formula=Sparsification.prune s.formula {f.core} ∧
          sp.right.formula=Sparsification.prune s.formula f.petals) :
      ∃ sp : Sparsification.Split s,
        listCNF (sparseBranch F (selectedFlower F p q h)).2.1=sp.left.formula ∧
        listCNF (sparseBranch F (selectedFlower F p q h)).2.2=sp.right.formula := by
    have hg := selectedFlower_good F p q h (by simpa using hx)
    let f := hg.toFlower
    let f' : Sparsification.Flower s.formula p q h := { f with
      cover := fun P hP => he ▸ f.cover P hP }
    obtain ⟨sp,hl,ht⟩ := hs f'
    have hc : f'.core=(selectedFlower F p q h).1.toFinset := by rfl
    have hp : f'.petals=listCNF (selectedFlower F p q h).2 := by rfl
    refine ⟨sp,?_,?_⟩ <;> simp only [sparseBranch,listCNF_prune]
    · rw [hl,hc,he]; rfl
    · rw [ht,hp,he]
  unfold sparseStep
  split
  · rename_i h2
    split
    · rename_i h32
      split
      · rename_i h31
        exact Or.inl ⟨rfl,rfl,rfl,hterm 1 1 _ (pow_pos hr _) h2,
          hterm 1 2 _ (pow_pos hr _) h31,hterm 2 1 _ (pow_pos hr _) h32⟩
      · rename_i h31
        exact Or.inr ⟨rfl,branch 1 2 _ h31 (Sparsification.split_from_three_unit hr s (hterm 1 1 _ (pow_pos hr _) h2))⟩
    · rename_i h32
      exact Or.inr ⟨rfl,branch 2 1 _ h32 (Sparsification.split_from_three_binary hr s (hterm 1 1 _ (pow_pos hr _) h2))⟩
  · rename_i h2
    exact Or.inr ⟨rfl,branch 1 1 _ h2 (Sparsification.split_from_two hr s)⟩

noncomputable def PolyProgram.sparseBranch (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (ClauseList α × FlowerRecord α) (SparseResult α) (fun x => Complexity.sparseBranch x.1 x.2) := by
  let fc : PolyProgram (ClauseList α × FlowerRecord α) (ClauseList α × ClauseList α) (fun x => (x.1,[x.2.1])) :=
    .expr (.pair TExpr.input.left (.pair TExpr.input.right.left .nil)) (by intro x; rfl)
  let fp : PolyProgram (ClauseList α × FlowerRecord α) (ClauseList α × ClauseList α) (fun x => (x.1,x.2.2)) :=
    .expr (.pair TExpr.input.left TExpr.input.right.right) (by intro x; rfl)
  exact ((PolyProgram.const false).pair ((fc.comp (PolyProgram.pruneList α)).pair
    (fp.comp (PolyProgram.pruneList α)))).congr (by intro x; rfl)

noncomputable def PolyProgram.sparseStep (α : Type) [TreeCodec α] [DecidableEq α] (r : ℕ) :
    PolyProgram (ClauseList α) (SparseResult α) (Complexity.sparseStep r) := by
  let test (p q h : ℕ) := (PolyProgram.flowerList α p q h).comp (PolyProgram.null (FlowerRecord α))
  let branch (p q h : ℕ) := (((PolyProgram.id (ClauseList α)).pair
    ((PolyProgram.flowerList α p q h).comp (PolyProgram.head (FlowerRecord α) ([],[])))).comp
      (PolyProgram.sparseBranch α))
  let done : PolyProgram (ClauseList α) (SparseResult α) (fun F => (true,F,F)) :=
    .expr (.pair (.const (boolTree true)) (.pair .input .input)) (by intro x; rfl)
  exact ((test 1 1 (r^2)).ite ((test 2 1 (r^4)).ite ((test 1 2 (r^4)).ite done
    (branch 1 2 (r^4))) (branch 2 1 (r^4))) (branch 1 1 (r^2))).congr (by intro F; rfl)

end ParityWL.Complexity

end OAI
