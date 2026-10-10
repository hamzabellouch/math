import OAI.Combinatorics.ParityLifts.GraphOutput

namespace OAI

namespace ParityWL.Complexity

def leafWords (t : ℕ) (F : BitFormula) : ℕ := 3*chunkWidth t F

def leafData (t : ℕ) (F : BitFormula) : ChoiceData t := bitChoiceData (bitGroup t F) (leafWords t F)

noncomputable def leafOutput (t : ℕ) (F : BitFormula) : List Bool :=
  (choiceWithWords (bitGroup t F,leafWords t F,words (leafWords t F))).output

noncomputable def PolyProgram.leafWords (t : ℕ) (ht : 0<t) :
    PolyProgram BitFormula ℕ (Complexity.leafWords t) :=
  (((PolyProgram.const 3).pair (PolyProgram.chunkWidth t ht)).comp PolyProgram.natMul).congr
    (by intro F; rfl)

noncomputable def PolyProgram.leafPrepare (t : ℕ) (ht : 0<t) :
    PolyProgram BitFormula ((Fin t → BitFormula) × ℕ) (fun F => (Complexity.bitGroup t F,Complexity.leafWords t F)) :=
  (PolyProgram.bitGroups t ht).pair (PolyProgram.leafWords t ht)

def TreeProgram.insertWords (t : ℕ) :
    TreeProgram ((Fin t → BitFormula) × ℕ) (TableInput t) (fun x => (x.1,x.2,Complexity.words x.2)) :=
  (TreeProgram.fst (Fin t → BitFormula) ℕ).pair
    ((TreeProgram.snd (Fin t → BitFormula) ℕ).pair
      ((TreeProgram.snd (Fin t → BitFormula) ℕ).comp TreeProgram.words))

noncomputable def PolyProgram.wordsOutput (t : ℕ) [NeZero t] :
    PolyProgram (TableInput t) (List Bool) (fun x => (Complexity.choiceWithWords x).output) :=
  ((PolyProgram.choiceWithWords t).comp (PolyProgram.graphOutput t)).congr (by intro x; rfl)

def TreeProgram.leafCompose (t : ℕ)
    (P : TreeProgram BitFormula ((Fin t → BitFormula) × ℕ)
      (fun F => (bitGroup t F,leafWords t F)))
    (Q : TreeProgram (TableInput t) (List Bool) (fun x => (choiceWithWords x).output)) :
    TreeProgram BitFormula (List Bool) (Complexity.leafOutput t) where
  code := .seq (.seq P.code (TreeProgram.insertWords t).code) Q.code
  time := fun F => P.time F+(TreeProgram.insertWords t).time (bitGroup t F,leafWords t F)+1+
    Q.time (bitGroup t F,leafWords t F,Complexity.words (leafWords t F))+1
  run := fun F => ((P.run F).seq ((TreeProgram.insertWords t).run (bitGroup t F,leafWords t F))).seq
    (Q.run (bitGroup t F,leafWords t F,Complexity.words (leafWords t F)))

noncomputable def TreeProgram.leafOutput (t : ℕ) [NeZero t] (ht : 0<t) :
    TreeProgram BitFormula (List Bool) (Complexity.leafOutput t) :=
  TreeProgram.leafCompose t (PolyProgram.leafPrepare t ht).program (PolyProgram.wordsOutput t).program

lemma leafData_success (t : ℕ) (ht : 0<t) (F : BitFormula) (hw : ∀ C∈F, C.length≤3) :
    (leafData t F).system.Successful ↔ ∃ a, bitSat a F := by
  rw [leafData,leafWords,bitChoiceData_correct _ _ (group_names_length t F hw)]
  exact exists_congr (fun a => bitGroup_sat t ht F a)

lemma leafData_size (t : ℕ) (F : BitFormula) :
    (leafData t F).system.SizeAtMost (2^leafWords t F+1) := by
  constructor
  · intro i
    change Fintype.card (Fin _ )≤_
    rw [Fintype.card_fin]
    change (List.map _ (satisfyingWords (leafWords t F) (bitGroup t F i))).length≤_
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans (by rw [length_words]; omega)
  · intro p
    change Fintype.card (Fin _)≤_
    rw [Fintype.card_fin]
    change (words (leafWords t F)).length+1≤_
    rw [length_words]

lemma leafOutput_spec (k : ℕ) (hk : 4≤k) (c : Convention) (F : BitFormula)
    (hw : ∀ C∈F, C.length≤3) :
    ∃ (n : ℕ) (G H : SimpleGraph (Fin n)),
      leafOutput (bagParameter c k) F=encodeGraphs G H ∧
      (∀ i, Equivalent G H c i k ↔ ¬ ∃ a, bitSat a F) ∧
      n≤(2^leafWords (bagParameter c k) F+1)*orderFactor (bagParameter c k) := by
  let t := bagParameter c k
  have ht : 0<t := by cases c <;> simp only [t,bagParameter] <;> omega
  obtain ⟨n,G,H,he,hg,hn⟩ := (leafData t F).output_spec k hk c
  refine ⟨n,G,H,he,fun i => (hg i).trans (not_congr (leafData_success t ht F hw)),?_⟩
  have hb := choice_lift_order_bound (show 2≤t by cases c <;> simp only [t,bagParameter] <;> omega)
    (leafData t F).system (2^leafWords t F+1) (leafData_size t F) (fun _ => 0)
  have hc := Fintype.card_congr ((leafData t F).vertexEquiv (fun _ => 0))
  simp only [Fintype.card_fin] at hc
  rw [hn,hc]
  exact hb

end ParityWL.Complexity

end OAI
