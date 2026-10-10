import OAI.Combinatorics.ContingencyTables.Sampling.SmallInverseRepairList
import OAI.Combinatorics.ContingencyTables.Sampling.SmallExchangeListProgram
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperLocalNeighbors

namespace OAI

/-! # A binary program for the full physical neighbor list -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def repairInput : Realizer (fun z : ProfileCheckData => (z.1.1,z.2)) :=
  pair (composition first first) second

lemma polynomial_repairInput : PolynomialTime repairInput :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second

def rawCodeNeighbors (z : ProfileCheckData) : List (List ℕ×List ℕ) :=
  codeExchangeList z.1.1.2 ++
    (forwardRepairList (z.1.1,z.2) ++ checkedInverseRepairList (z.1.1,z.2))

def rawCodeNeighborsRealizer : Realizer rawCodeNeighbors :=
  composition (pair (composition profileViews codeExchangeListRealizer)
    (composition (pair (composition repairInput forwardRepairListRealizer)
      (composition repairInput checkedInverseRepairListRealizer)) append)) append

lemma polynomial_rawCodeNeighbors : PolynomialTime rawCodeNeighborsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_profileViews polynomial_codeExchangeList)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_repairInput polynomial_forwardRepairList)
      (polynomial_composition polynomial_repairInput polynomial_checkedInverseRepairList))
      polynomial_append)) polynomial_append

def candidateData (z : ProfileCheckData×(List ℕ×List ℕ)) : ProfileCheckData :=
  (((z.1.1.1.1,z.2),z.1.1.2),z.1.2)

def candidateDataRealizer : Realizer candidateData :=
  pair (pair (pair (composition (f := fun z : ProfileCheckData×(List ℕ×List ℕ) => z.1)
    (g := fun z : ProfileCheckData => z.1.1.1) first profileCatalog) second)
    (composition (f := fun z : ProfileCheckData×(List ℕ×List ℕ) => z.1)
      (g := fun z : ProfileCheckData => z.1.2) first profileMargins)) (composition first second)

lemma polynomial_candidateData : PolynomialTime candidateDataRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_profileCatalog) polynomial_second)
    (polynomial_composition polynomial_first polynomial_profileMargins))
    (polynomial_composition polynomial_first polynomial_second)

def codeNeighbors (z : ProfileCheckData) : List (List ℕ×List ℕ) :=
  ((rawCodeNeighbors z).filter (fun v => profileTest (candidateData (z,v)))).dedup

def codeNeighborsRealizer : Realizer codeNeighbors :=
  composition (composition (pair identity rawCodeNeighborsRealizer)
    (filterWith (composition candidateDataRealizer profileTestRealizer))) profileCodeDedup

theorem polynomial_codeNeighbors : PolynomialTime codeNeighborsRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_rawCodeNeighbors)
    (polynomial_filterWith (polynomial_composition polynomial_candidateData polynomial_profileTest)))
    polynomial_profileCodeDedup

lemma codeNeighbors_nodup (z : ProfileCheckData) : (codeNeighbors z).Nodup :=
  List.nodup_dedup _

theorem codeNeighbors_length (z : ProfileCheckData) (q : ℕ)
    (hx : z.1.1.2.1.length=q) (hy : z.1.1.2.2.length=q) :
    (codeNeighbors z).length≤6*q^2 := by
  have h0 := ((rawCodeNeighbors z).filter
    (fun v => profileTest (candidateData (z,v)))).dedup_sublist.length_le
  have h1 := List.length_filter_le (fun v => profileTest (candidateData (z,v))) (rawCodeNeighbors z)
  have he := codeExchangeList_length z.1.1.2
  have hf := forwardRepairList_length (z.1.1,z.2)
  have hb := checkedInverseRepairList_length (z.1.1,z.2)
  change (codeNeighbors z).length≤_ at h0
  simp only [rawCodeNeighbors,List.length_append] at h1
  simp only [hx,hy] at he hf hb
  have ht := h0.trans h1
  nlinarith [ht]

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n q : ℕ}

theorem mem_rawCodeNeighbors (r : Fin m → ℕ) (c : Fin n → ℕ)
    (e : Fin q ≃ Cells (paperSmall r c)) (x y : PaperStates r c) :
    profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := Fin m) (J := Fin n))^12) y) ∈
        rawCodeNeighbors (codeCheckData (cellCatalog (paperSmall r c) e)
          (List.ofFn r) (List.ofFn c) ((dimensionAllowance (I := Fin m) (J := Fin n))^20)
          (profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
            ((dimensionAllowance (I := Fin m) (J := Fin n))^12) x))) ↔
      ArithmeticEdge r c
        (physicalProfile (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := Fin m) (J := Fin n))^12) x)
        (physicalProfile (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := Fin m) (J := Fin n))^12) y) := by
  let small := paperSmall r c
  let B := stateCapacity r c
  let U := (dimensionAllowance (I := Fin m) (J := Fin n))^20
  let L := (dimensionAllowance (I := Fin m) (J := Fin n))^12
  let v := physicalProfile small B r c L x
  let w := physicalProfile small B r c L y
  have hU : ∀ a : Cells small,B a.val.1 a.val.2=U :=
    fun a => stateCapacity_small r c _ _ a.property
  have hv : ∀ a : Cells small,v (a,true)≤B a.val.1 a.val.2 :=
    fun a => (physicalProfile_feasible r c x).bounded (a,true)
  have hw : ∀ a,w a≤B a.1.val.1 a.1.val.2 := (physicalProfile_feasible r c y).bounded
  change profileCode small e w ∈ rawCodeNeighbors
    (codeCheckData (cellCatalog small e) (List.ofFn r) (List.ofFn c) U (profileCode small e v)) ↔
      ArithmeticEdge r c v w
  simp only [rawCodeNeighbors,codeCheckData,List.mem_append]
  rw [mem_codeExchangeList,mem_forwardRepairList small e B U hU v hv,
    mem_checkedInverseRepairList small e B U hU v w hw]
  simp only [(profileCode_injective small e).eq_iff,ArithmeticEdge,ArithmeticRepair,Prod.exists]
  rfl

theorem mem_codeNeighbors (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (e : Fin q ≃ Cells (paperSmall r c)) (x y : PaperStates r c) :
    profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := Fin m) (J := Fin n))^12) y) ∈
        codeNeighbors (codeCheckData (cellCatalog (paperSmall r c) e)
          (List.ofFn r) (List.ofFn c) ((dimensionAllowance (I := Fin m) (J := Fin n))^20)
          (profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
            ((dimensionAllowance (I := Fin m) (J := Fin n))^12) x))) ↔
      physicalAdjacent r c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)
        ((dimensionAllowance (I := Fin m) (J := Fin n))^12) (stateCapacity r c)
        (stateCapacity_small r c) x y := by
  rw [codeNeighbors,List.mem_dedup,List.mem_filter]
  have hp := (profileTest_iff r c htotal e
    (physicalProfile (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := Fin m) (J := Fin n))^12) y)).mpr (physicalProfile_feasible r c y)
  change _ ∧ _ ↔ _
  have hc : profileTest (candidateData
      (codeCheckData (cellCatalog (paperSmall r c) e) (List.ofFn r) (List.ofFn c)
        ((dimensionAllowance (I := Fin m) (J := Fin n))^20)
        (profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := Fin m) (J := Fin n))^12) x)),
        profileCode (paperSmall r c) e (physicalProfile (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := Fin m) (J := Fin n))^12) y)))=true := hp
  simp only [hc,and_true]
  rw [mem_rawCodeNeighbors,arithmeticEdge_iff]

end
end ContingencyTables.SmallGraphProfiles

end OAI
