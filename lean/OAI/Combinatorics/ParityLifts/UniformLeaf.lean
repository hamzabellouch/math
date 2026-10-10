import OAI.Combinatorics.ParityLifts.ParamTags

namespace OAI

namespace ParityWL.Complexity

abbrev TagPair := List RawTag × List RawTag
abbrev RawLeafPreparation := (List BitFormula × TagPair) × ℕ
abbrev RawLeafTable := (List BitFormula × TagPair) × ℕ × List (List Bool)

noncomputable def ParamPolyProgram.tags (α : Type) [TreeCodec α] :
    ParamPolyProgram ℕ α TagPair (fun t _ => (rawTags t false,rawTags t true)) where
  program := (TreeProgram.fst ℕ α).comp TreeProgram.tagPair
  coefficient := fun t => TreeProgram.tagPair.time t+2
  degree := fun _ => 1
  bound := by
    intro t x
    change (treeEncode (t,x)).size+TreeProgram.tagPair.time t+1≤_
    simp only [pow_one]
    nlinarith

noncomputable def ParamPolyProgram.rawPreparation :
    ParamPolyProgram ℕ BitFormula RawLeafPreparation
      (fun t F => ((rawGroups t F,(rawTags t false,rawTags t true)),leafWords t F)) := by
  let G := ParamPolyProgram.ofPoly PolyProgram.rawGroups
  let W := ParamPolyProgram.ofPoly (f := fun t F => Complexity.leafWords t F) (((PolyProgram.const 3).pair PolyProgram.runtimeChunkWidth).comp PolyProgram.natMul)
  exact (G.pair (ParamPolyProgram.tags BitFormula)).pair W

def TreeProgram.addWords (α : Type) [TreeCodec α] :
    TreeProgram (α × ℕ) (α × ℕ × List (List Bool)) (fun x => (x.1,x.2,Complexity.words x.2)) :=
  (TreeProgram.fst α ℕ).pair ((TreeProgram.snd α ℕ).pair ((TreeProgram.snd α ℕ).comp TreeProgram.words))

noncomputable def PolyProgram.rawWordsOutput : PolyProgram RawLeafTable (List Bool)
    (fun x => Complexity.rawOutput (Complexity.rawChoiceWithWords (x.1.1,x.2)) x.1.2) := by
  let I : PolyProgram RawLeafTable RawTableInput (fun x => (x.1.1,x.2)) :=
    .expr (.pair TExpr.input.left.left TExpr.input.right) (by intro x; rfl)
  let T : PolyProgram RawLeafTable TagPair (fun x => x.1.2) :=
    .expr TExpr.input.left.right (by intro x; rfl)
  exact ((I.comp PolyProgram.rawChoiceWithWords).pair T).comp PolyProgram.rawOutput

def uniformLeafOutput (t : ℕ) (F : BitFormula) : List Bool :=
  rawOutput (rawLeafData t F) (rawTags t false,rawTags t true)

noncomputable def TreeProgram.uniformLeafOutput : TreeProgram (ℕ × BitFormula) (List Bool)
    (fun x => Complexity.uniformLeafOutput x.1 x.2) :=
  ((ParamPolyProgram.rawPreparation.program.comp (TreeProgram.addWords (List BitFormula × TagPair))).comp
    PolyProgram.rawWordsOutput.program).congr (by intro x; rfl)

lemma addWords_time {α : Type} [TreeCodec α] (x : α × ℕ) :
    (TreeProgram.addWords α).time x=TreeProgram.words.time x.2+3*(treeEncode x).size+3 := by
  simp only [TreeProgram.addWords,TreeProgram.pair,TreeProgram.comp,TreeProgram.fst,TreeProgram.snd]
  omega

lemma addWords_size {α : Type} [TreeCodec α] (x : α × ℕ) :
    (treeEncode (x.1,x.2,words x.2)).size+1 ≤ 10*((treeEncode x).size+1)*2^x.2 := by
  obtain ⟨a,q⟩ := x
  have hw := words_size q
  have hp : 1≤2^q := Nat.one_le_two_pow
  simp only [treeEncode_pair,treeEncode_nat,numTree_size,DataTree.size] at *
  nlinarith [DataTree.size_pos (treeEncode a)]

theorem uniformLeafOutput_bound : ∃ E : ℕ, 0<E ∧ ∀ t : ℕ, ∃ C d : ℕ,
    0<C ∧ ∀ F : BitFormula, TreeProgram.uniformLeafOutput.time (t,F) ≤
      C*((treeEncode (t,F)).size+1)^d*2^(E*leafWords t F) := by
  obtain ⟨W,e,hw⟩ := TreeProgram.words_bound
  let P := ParamPolyProgram.rawPreparation
  let Q := PolyProgram.rawWordsOutput
  let D := Q.degree
  refine ⟨e+D+1,by omega,?_⟩
  intro t
  refine ⟨P.coefficient t+4*(P.coefficient t+1)+(W+8)*(P.coefficient t+1)^e+
      Q.coefficient*(10*(P.coefficient t+1))^D+3,P.degree t*(e+D+1),by omega,?_⟩
  intro F
  change P.program.time (t,F)+(TreeProgram.addWords (List BitFormula × TagPair)).time
      ((rawGroups t F,(rawTags t false,rawTags t true)),leafWords t F)+1+
    Q.program.time (((rawGroups t F,(rawTags t false,rawTags t true)),leafWords t F,words (leafWords t F)))+1≤_
  apply leaf_numeric_bound
  · omega
  · exact P.bound t F
  · have hz := (P.program.run (t,F)).bounds.2.1
    exact Nat.add_le_add_right hz 1
  · simp only [treeEncode_pair,treeEncode_nat,numTree_size,DataTree.size]
    omega
  · rw [addWords_time]
    have hh := hw (leafWords t F)
    change TreeProgram.words.time (leafWords t F)+3*(treeEncode ((rawGroups t F,rawTags t false,rawTags t true),leafWords t F)).size+3 ≤ _
    dsimp only at *
    omega
  · exact addWords_size _
  · exact Q.bound _

theorem uniformLeafOutput_spec (k : ℕ) (hk : 4≤k) (c : Convention) (F : BitFormula)
    (hw : ∀ C∈F,C.length≤3) :
    ∃ (n : ℕ) (G H : SimpleGraph (Fin n)),
      uniformLeafOutput (bagParameter c k) F=encodeGraphs G H ∧
      (∀ i,Equivalent G H c i k ↔ ¬∃ a,bitSat a F) ∧
      n≤(2^leafWords (bagParameter c k) F+1)*orderFactor (bagParameter c k) := by
  let t := bagParameter c k
  have ht : 0<t := by cases c <;> simp only [t,bagParameter] <;> omega
  obtain ⟨n,G,H,he,hg,hn⟩ := rawOutput_spec k hk c (leafData t F)
  refine ⟨n,G,H,?_,fun i => (hg i).trans (not_congr (leafData_success t ht F hw)),?_⟩
  · simpa only [uniformLeafOutput,rawLeafData_eq] using he
  · have hc := Fintype.card_congr (rawIndexEquiv (leafData t F) false)
    simp only [Fintype.card_fin,tagCharge_false] at hc
    rw [hn,hc]
    exact choice_lift_order_bound (by cases c <;> simp only [t,bagParameter] <;> omega)
      (leafData t F).system (2^leafWords t F+1) (leafData_size t F) (fun _ => 0)

end ParityWL.Complexity

end OAI
