import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorExecution

namespace OAI

/-! # Computed sizes of the estimator's disjoint word banks

The schedule supplies the phase and sample counts and the two walk times.
The catalog itself supplies both the integer-draw widths and the initial
free-assignment count. No list is allocated from a binary count here.
-/

namespace ContingencyTables.RootedEstimatorLayoutProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev State := RootedOracleWalkProgram.State
abbrev Schedule := (ℕ×ℕ)×((ℕ×ℕ)×ℕ)
abbrev Context := State×Schedule

def stepWidth (z : Context) : ℕ := RootedOracleWalkProgram.stepWidth z.1.1
def stepWidthRealizer : Realizer stepWidth :=
  composition (f := fun z : Context => z.1.1) (g := RootedOracleWalkProgram.stepWidth)
    (composition first first) RootedOracleWalkProgram.stepWidthRealizer
lemma polynomial_stepWidth : PolynomialTime stepWidthRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    RootedOracleWalkProgram.polynomial_stepWidth

def ratioWidth (z : Context) : ℕ := z.2.2.1.1*stepWidth z
def ratioWidthRealizer : Realizer ratioWidth :=
  composition (f := fun z : Context => (z.2.2.1.1,stepWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (composition (composition second second) first) first) stepWidthRealizer)
    multiply
lemma polynomial_ratioWidth : PolynomialTime ratioWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_second) polynomial_first) polynomial_first)
    polynomial_stepWidth) polynomial_multiply

def ratioBlockWidth (z : Context) : ℕ := z.2.1.2*ratioWidth z
def ratioBlockWidthRealizer : Realizer ratioBlockWidth :=
  composition (f := fun z : Context => (z.2.1.2,ratioWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (composition second first) second) ratioWidthRealizer) multiply
lemma polynomial_ratioBlockWidth : PolynomialTime ratioBlockWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second)
    polynomial_ratioWidth) polynomial_multiply

def ratioBankWidth (z : Context) : ℕ := z.2.1.1*ratioBlockWidth z
def ratioBankWidthRealizer : Realizer ratioBankWidth :=
  composition (f := fun z : Context => (z.2.1.1,ratioBlockWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (composition second first) first) ratioBlockWidthRealizer) multiply
lemma polynomial_ratioBankWidth : PolynomialTime ratioBankWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_first)
    polynomial_ratioBlockWidth) polynomial_multiply

def binFrame (z : Context) : RootedBinFramesProgram.Input :=
  ((z.1.1.1,(z.2.2.2,z.1.1.2.1.1.1)),(z.1.1.2.2.1,z.1.2))
def binFrameRealizer : Realizer binFrame := by
  let k : Realizer (fun z : Context => z.1.1.1) := composition (composition first first) first
  let h : Realizer (fun z : Context => z.2.2.2) := composition (composition second second) second
  let d : Realizer (fun z : Context => z.1.1.2.1.1.1) :=
    composition (composition (composition (composition (composition first first) second) first) first) first
  let catalog : Realizer (fun z : Context => z.1.1.2.2.1) :=
    composition (composition (composition (composition first first) second) second) first
  exact pair (pair k (pair h d)) (pair catalog (composition first second))
lemma polynomial_binFrame : PolynomialTime binFrameRealizer := by
  unfold binFrameRealizer
  exact polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_second)
        (polynomial_composition (polynomial_composition (polynomial_composition
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_second) polynomial_first) polynomial_first) polynomial_first)))
    (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
          polynomial_second) polynomial_first)
      (polynomial_composition polynomial_first polynomial_second))

def frames (z : Context) : List BinVectorProgram.Frame := RootedBinFramesProgram.frames (binFrame z)
def framesRealizer : Realizer frames :=
  composition (f := binFrame) (g := RootedBinFramesProgram.frames)
    binFrameRealizer RootedBinFramesProgram.framesRealizer
lemma polynomial_frames : PolynomialTime framesRealizer :=
  polynomial_composition polynomial_binFrame RootedBinFramesProgram.polynomial_frames

attribute [local irreducible] frames

def binWidth (z : Context) : ℕ := ((frames z).map BinVectorProgram.reservedWidth).sum
def binWidthRealizer : Realizer binWidth :=
  composition (f := frames) (g := fun xs : List BinVectorProgram.Frame =>
    (xs.map BinVectorProgram.reservedWidth).sum) framesRealizer
    (composition (map BinVectorProgram.reservedWidthRealizer) listSum)
lemma polynomial_binWidth : PolynomialTime binWidthRealizer :=
  polynomial_composition polynomial_frames
    (polynomial_composition (polynomial_map BinVectorProgram.polynomial_reservedWidth) polynomial_listSum)

def assignmentCount (z : Context) : ℕ := ((frames z).map (fun x => x.1.1.2)).prod
def rangeValue (x : BinVectorProgram.Frame) : ℕ := x.1.1.2
def rangeValueRealizer : Realizer rangeValue := composition (composition first first) second
lemma polynomial_rangeValue : PolynomialTime rangeValueRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second

def rangeValues (xs : List BinVectorProgram.Frame) : List ℕ := xs.map rangeValue
def rangeValuesRealizer : Realizer rangeValues := MatchingFPRAS.TreeTyped.map rangeValueRealizer
lemma polynomial_rangeValues : PolynomialTime rangeValuesRealizer := polynomial_map polynomial_rangeValue

attribute [local irreducible] rangeValue rangeValues

def assignmentCountRealizer : Realizer assignmentCount := by
  let values : Realizer (fun z : Context => rangeValues (frames z)) :=
    composition (f := frames) (g := rangeValues) framesRealizer rangeValuesRealizer
  exact (composition (f := fun z : Context => rangeValues (frames z))
    (g := (List.prod : List ℕ → ℕ)) values listProd).congr (by
      intro z
      unfold assignmentCount rangeValues rangeValue
      rfl)
lemma polynomial_assignmentCount : PolynomialTime assignmentCountRealizer := by
  unfold assignmentCountRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition polynomial_frames polynomial_rangeValues)
    polynomial_listProd

def correctionWalkWidth (z : Context) : ℕ := z.2.2.1.2*stepWidth z
def correctionWalkWidthRealizer : Realizer correctionWalkWidth :=
  composition (f := fun z : Context => (z.2.2.1.2,stepWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (composition (composition second second) first) second) stepWidthRealizer)
    multiply
lemma polynomial_correctionWalkWidth : PolynomialTime correctionWalkWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_second) polynomial_first) polynomial_second)
    polynomial_stepWidth) polynomial_multiply

def correctionWidth (z : Context) : ℕ := correctionWalkWidth z+binWidth z
def correctionWidthRealizer : Realizer correctionWidth :=
  composition (f := fun z : Context => (correctionWalkWidth z,binWidth z))
    (g := fun p : ℕ×ℕ => p.1+p.2) (pair correctionWalkWidthRealizer binWidthRealizer) add
lemma polynomial_correctionWidth : PolynomialTime correctionWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_correctionWalkWidth polynomial_binWidth) polynomial_add

def wordWidth (z : Context) : ℕ := ratioBankWidth z+z.2.1.2*correctionWidth z
def wordWidthRealizer : Realizer wordWidth :=
  composition (f := fun z : Context => (ratioBankWidth z,z.2.1.2*correctionWidth z))
    (g := fun p : ℕ×ℕ => p.1+p.2) (pair ratioBankWidthRealizer
      (composition (f := fun z : Context => (z.2.1.2,correctionWidth z))
        (g := fun p : ℕ×ℕ => p.1*p.2)
        (pair (composition (composition second first) second) correctionWidthRealizer) multiply)) add
lemma polynomial_wordWidth : PolynomialTime wordWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_ratioBankWidth
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second)
      polynomial_correctionWidth) polynomial_multiply)) polynomial_add

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Context :=
  (RootedOracleWalkProgram.data A C 0 K z v,((j,S),((Tr,Tc),h)))

lemma frames_data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    frames (data A C K j S Tr Tc h z v)=List.ofFn (fun i =>
      (((K,CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i)),
        (v i).val.toNat),(h,A.d))) := by
  unfold frames
  change RootedBinFramesProgram.frames (RootedBinFramesProgram.data A h v)=_
  exact RootedBinFramesProgram.frames_data A h v

lemma binWidth_data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    binWidth (data A C K j S Tr Tc h z v)=RootedBinDrawLaw.wordBits A h := by
  rw [binWidth,frames_data]
  simp only [List.map_ofFn,List.sum_ofFn,BinVectorProgram.reservedWidth,
    RootedBinDrawLaw.wordBits,FairBits.offsetBitLength,Function.comp_apply]

lemma assignmentCount_data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    assignmentCount (data A C K j S Tr Tc h z v)=CompanionOracleDensity.assignmentCount A := by
  rw [assignmentCount,frames_data,CompanionOracleDensity.assignmentCount_eq_prod]
  simp only [List.map_ofFn,List.prod_ofFn]
  exact Fintype.prod_equiv (RootedForestCatalog.freeEquiv A) _ _ (fun _ => rfl)

lemma ratioWidth_data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    ratioWidth (data A C K j S Tr Tc h z v)=Tr*CompanionOracleDensity.oracleStepBits A C := by
  change Tr*RootedOracleWalkProgram.stepWidth (RootedOracleWalkProgram.data A C 0 K z v).1=_
  rw [RootedOracleWalkProgram.stepWidth_data]

lemma correctionWalkWidth_data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    correctionWalkWidth (data A C K j S Tr Tc h z v)=Tc*CompanionOracleDensity.oracleStepBits A C := by
  change Tc*RootedOracleWalkProgram.stepWidth (RootedOracleWalkProgram.data A C 0 K z v).1=_
  rw [RootedOracleWalkProgram.stepWidth_data]

end
end ContingencyTables.RootedEstimatorLayoutProgram

end OAI
