import OAI.Combinatorics.ContingencyTables.Machines.FlowPathProgram

namespace OAI

/-! # Binary signed augmentation of one matrix entry -/

namespace ContingencyTables.FlowEntryProgram

open MatchingFPRAS.TreeTyped ResidualGraphProgram SignedPairProgram FlowPathProgram

abbrev UpdateData := Data×(List (ℕ×ℕ)×ℕ)
abbrev EntryInput := UpdateData×(ℕ×ℕ)
abbrev RawInput := Signed×(ℕ×(ℕ×ℕ))

def rawUpdate (z : RawInput) : Signed :=
  (z.1.1+z.2.1*z.2.2.1,z.1.2+z.2.1*z.2.2.2)

def rawUpdateRealizer : Realizer rawUpdate := by
  let old : Realizer (fun z : RawInput=>z.1) := first
  let a : Realizer (fun z : RawInput=>z.2.1) := composition second first
  let f : Realizer (fun z : RawInput=>z.2.2.1) := composition (composition second second) first
  let b : Realizer (fun z : RawInput=>z.2.2.2) := composition (composition second second) second
  exact composition (pair old (pair (composition (pair a f) multiply)
    (composition (pair a b) multiply))) plusRealizer

lemma polynomial_rawUpdate : PolynomialTime rawUpdateRealizer := by
  unfold rawUpdateRealizer
  apply polynomial_composition
  · apply polynomial_pair polynomial_first
    apply polynomial_pair
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_first)
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_first)) polynomial_multiply
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_first)
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_second)) polynomial_multiply
  · exact polynomial_plus

lemma rawUpdate_value (old : Signed) (a f b : ℕ) :
    SignedPairProgram.value (rawUpdate (old,(a,(f,b))))=
      SignedPairProgram.value old+(a:ℤ)*((f:ℤ)-b) := by
  simp only [rawUpdate,SignedPairProgram.value,Nat.cast_add,Nat.cast_mul]
  ring

def limits (z : EntryInput) : ℕ×ℕ :=
  (capacityEntry (z.1.1.1,z.2),capacityEntry (z.1.1.1,(z.2.2,z.2.1)))

def limitsRealizer : Realizer limits := by
  let C : Realizer (fun z : EntryInput=>z.1.1.1) := composition (composition first first) first
  let uv : Realizer (fun z : EntryInput=>z.2) := second
  let vu : Realizer (fun z : EntryInput=>(z.2.2,z.2.1)) :=
    pair (composition second second) (composition second first)
  exact pair (composition (pair C uv) capacityEntryRealizer)
    (composition (pair C vu) capacityEntryRealizer)

lemma polynomial_limits : PolynomialTime limitsRealizer := by
  unfold limitsRealizer
  apply polynomial_pair
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first) polynomial_second) polynomial_capacityEntry
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
        (polynomial_composition polynomial_second polynomial_first))) polynomial_capacityEntry

def rawInput (z : EntryInput) : RawInput :=
  (flowEntry (z.1.1.2,z.2),(z.1.2.2,
    (arcCount (z.2,z.1.2.1),arcCount ((z.2.2,z.2.1),z.1.2.1))))

def rawInputRealizer : Realizer rawInput := by
  let F : Realizer (fun z : EntryInput=>z.1.1.2) :=
    composition (composition first first) second
  let as : Realizer (fun z : EntryInput=>z.1.2.1) :=
    composition (composition first second) first
  let a : Realizer (fun z : EntryInput=>z.1.2.2) :=
    composition (composition first second) second
  let uv : Realizer (fun z : EntryInput=>z.2) := second
  let vu : Realizer (fun z : EntryInput=>(z.2.2,z.2.1)) :=
    pair (composition second second) (composition second first)
  let forward : Realizer (fun z : EntryInput => arcCount (z.2,z.1.2.1)) :=
    composition (f := fun z : EntryInput => (z.2,z.1.2.1))
      (g := FlowPathProgram.arcCount) (pair uv as) arcCountRealizer
  let backward : Realizer (fun z : EntryInput => arcCount ((z.2.2,z.2.1),z.1.2.1)) :=
    composition (f := fun z : EntryInput => ((z.2.2,z.2.1),z.1.2.1))
      (g := FlowPathProgram.arcCount) (pair vu as) arcCountRealizer
  exact pair (composition (pair F uv) flowEntryRealizer)
    (pair a (pair forward backward))

lemma polynomial_rawInput : PolynomialTime rawInputRealizer := by
  unfold rawInputRealizer
  apply polynomial_pair
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_second) polynomial_flowEntry
  · apply polynomial_pair
    · exact polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_second
    · apply polynomial_pair
      · exact polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
            polynomial_first)) polynomial_arcCount
      · exact polynomial_composition (polynomial_pair
          (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
            (polynomial_composition polynomial_second polynomial_first))
          (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
            polynomial_first)) polynomial_arcCount

def updateCell (z : EntryInput) : Signed :=
  FlowClamp.clamp (limits z,rawUpdate (rawInput z))

def updateCellRealizer : Realizer updateCell :=
  composition (pair limitsRealizer (composition rawInputRealizer rawUpdateRealizer))
    FlowClamp.clampRealizer

lemma polynomial_updateCell : PolynomialTime updateCellRealizer :=
  polynomial_composition (polynomial_pair polynomial_limits
    (polynomial_composition polynomial_rawInput polynomial_rawUpdate)) FlowClamp.polynomial_clamp

lemma updateCell_bounds (z : EntryInput) :
    (updateCell z).1≤(limits z).1 ∧ (updateCell z).2≤(limits z).2 :=
  FlowClamp.clamp_bounds _ _

lemma arcCount_map {n : ℕ} (u v : Fin n) (xs : List (Fin n×Fin n)) :
    (arcCount ((u.val,v.val),xs.map (fun xy=>(xy.1.val,xy.2.val))):ℤ)=
      (xs.map (fun xy=>if xy=(u,v) then (1:ℤ) else 0)).sum := by
  rw [arcCount_cast,List.map_map]
  congr 1
  apply List.map_congr_left
  intro xy _
  simp only [Function.comp_apply,Fin.val_inj,Prod.ext_iff]

lemma updateCell_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (f : PublishedEdmondsKarp.Flow n) (xs : List (Fin n)) (a : ℕ)
    (hnew : PublishedEdmondsKarp.Feasible c s t
      (ResidualAugmentation.listUpdate f xs (a:ℤ))) (u v : Fin n) :
    updateCell (((natCode c,flowCode f),
      ((ResidualAugmentation.arcs xs).map (fun uv=>(uv.1.val,uv.2.val)),a)),(u.val,v.val))=
      ForestAffineProgram.signedParts (ResidualAugmentation.listUpdate f xs (a:ℤ) u v) := by
  unfold updateCell limits rawInput
  rw [capacityEntry_code,capacityEntry_code,flowEntry_code]
  apply FlowClamp.clamp_feasible c s t _ hnew u v
  rw [rawUpdate_value,arcCount_map,arcCount_map]
  simp only [SignedPairProgram.value,ForestAffineProgram.signedParts_sub,
    ResidualAugmentation.listUpdate]

end ContingencyTables.FlowEntryProgram

end OAI
