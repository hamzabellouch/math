import OAI.Combinatorics.ParityLifts.UniformDFS

namespace OAI

namespace ParityWL.Complexity

lemma map_range_ofFn {α : Type} (t : ℕ) (f : ℕ → α) :
    (List.range t).map f=List.ofFn (fun i : Fin t => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

abbrev RawTableInput := List BitFormula × ℕ × List (List Bool)

def rawPairKey (Q : List BitFormula) (d i j : ℕ) (bs : List Bool) : List Bool :=
  let lo := names (Q[min i j]?.getD [])
  let hi := names (Q[max i j]?.getD [])
  lo.map (fun v => if v∈hi then lookupBits (names (Q[i]?.getD [])) bs v else false) ++
    List.replicate (d-lo.length) false

lemma rawPairKey_ofFn {t : ℕ} (Q : Fin t → BitFormula) (d : ℕ) (i j : Fin t) (bs : List Bool) :
    rawPairKey (List.ofFn Q) d i.val j.val bs=pairKey Q d i j bs := by
  have hi : min i.val j.val<t := (min_le_left _ _).trans_lt i.isLt
  have hj : max i.val j.val<t := max_lt i.isLt j.isLt
  dsimp only [rawPairKey,pairKey]
  simp only [List.getElem?_ofFn,hi,hj,i.isLt,↓reduceDIte,Option.getD_some,Fin.eta]
  rfl

def rawRowKey (x : RawTableInput) (i : ℕ) (bs : List Bool) : List ℕ :=
  (List.range x.1.length).map (fun j => x.2.2.idxOf (rawPairKey x.1 x.2.1 i j bs))

def rawDomain (x : RawTableInput) (i : ℕ) : List (List ℕ) :=
  (x.2.2.filter (fun bs => (x.1[i]?.getD []).all (fun C => C.any
    (fun l => lookupBits (names (x.1[i]?.getD [])) bs l.1 == l.2)))).map (rawRowKey x i)

def rawChoiceWithWords (x : RawTableInput) : RawChoiceData :=
  ((List.range x.1.length).map (rawDomain x),
    (List.range x.1.length).map (fun _ => (List.range x.1.length).map (fun _ => x.2.2.length)))

lemma rawChoiceWithWords_ofFn {t : ℕ} (x : TableInput t) :
    rawChoiceWithWords (List.ofFn x.1,x.2)=(choiceWithWords x).raw := by
  have hrow (i : Fin t) (bs : List Bool) :
      rawRowKey (List.ofFn x.1,x.2) i.val bs=
        List.ofFn (fun j => x.2.2.idxOf (pairKey x.1 x.2.1 i j bs)) := by
    simp only [rawRowKey,List.length_ofFn,map_range_ofFn,rawPairKey_ofFn]
  dsimp only [rawChoiceWithWords,ChoiceData.raw,choiceWithWords]
  simp only [List.length_ofFn,map_range_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  dsimp only [rawDomain]
  simp only [List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some,Fin.eta,List.map_map]
  apply List.map_congr_left
  intro bs _
  exact hrow i bs

def rawGroups (t : ℕ) (F : BitFormula) : List BitFormula :=
  (List.range t).map (fun i => (F.drop (i*chunkWidth t F)).take (chunkWidth t F))

lemma rawGroups_ofFn (t : ℕ) (F : BitFormula) : rawGroups t F=List.ofFn (bitGroup t F) := by
  rw [rawGroups,map_range_ofFn]
  rfl

def rawLeafData (t : ℕ) (F : BitFormula) : RawChoiceData :=
  rawChoiceWithWords (rawGroups t F,leafWords t F,words (leafWords t F))

lemma rawLeafData_eq (t : ℕ) (F : BitFormula) : rawLeafData t F=(leafData t F).raw := by
  rw [rawLeafData,rawGroups_ofFn]
  exact rawChoiceWithWords_ofFn (bitGroup t F,leafWords t F,words (leafWords t F))

end ParityWL.Complexity

end OAI
