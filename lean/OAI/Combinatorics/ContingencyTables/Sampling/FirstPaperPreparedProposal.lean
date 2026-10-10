import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperComputedCatalog

namespace OAI

/-! # Preparing the complete proposal input from binary margin lists -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def squareNat : Realizer (fun n : ℕ => n*n) :=
  composition (pair identity identity) multiply

lemma polynomial_squareNat : PolynomialTime squareNat :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_identity) polynomial_multiply

def fourthPower : Realizer (fun n : ℕ => n^4) :=
  (composition squareNat squareNat).congr (by intro n; simp only [Function.comp_apply]; ring)

lemma polynomial_fourthPower : PolynomialTime fourthPower :=
  polynomial_congr _ (polynomial_composition polynomial_squareNat polynomial_squareNat)

def fifthPower : Realizer (fun n : ℕ => n^5) :=
  (composition (pair fourthPower identity) multiply).congr
    (by intro n; simp only [Function.comp_apply,id_eq,pow_succ])

lemma polynomial_fifthPower : PolynomialTime fifthPower :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_fourthPower polynomial_identity) polynomial_multiply)

def twentiethPower : Realizer (fun n : ℕ => n^20) :=
  (composition fifthPower fourthPower).congr (by
    intro n
    simp only [Function.comp_apply,←pow_mul])

lemma polynomial_twentiethPower : PolynomialTime twentiethPower :=
  polynomial_congr _ (polynomial_composition polynomial_fifthPower polynomial_fourthPower)

def marginDimension (z : List ℕ×List ℕ) : ℕ := 10+(z.1.length+1)*(z.2.length+1)

def marginDimensionRealizer : Realizer marginDimension :=
  composition (f := fun z : List ℕ×List ℕ => (10,(z.1.length+1)*(z.2.length+1)))
    (g := fun z : ℕ×ℕ => z.1+z.2) (pair (constant 10)
    (composition (f := fun z : List ℕ×List ℕ => (z.1.length+1,z.2.length+1))
      (g := fun z : ℕ×ℕ => z.1*z.2)
      (pair (composition (composition first listLength) successor)
      (composition (composition second listLength) successor)) multiply)) add

theorem polynomial_marginDimension : PolynomialTime marginDimensionRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 10)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_listLength)
        polynomial_successor)
      (polynomial_composition (polynomial_composition polynomial_second polynomial_listLength)
        polynomial_successor)) polynomial_multiply)) polynomial_add

def marginThreshold (z : List ℕ×List ℕ) : ℕ := (marginDimension z)^20

def marginThresholdRealizer : Realizer marginThreshold :=
  composition (f := marginDimension) (g := fun n : ℕ => n^20) marginDimensionRealizer twentiethPower

theorem polynomial_marginThreshold : PolynomialTime marginThresholdRealizer :=
  polynomial_composition polynomial_marginDimension polynomial_twentiethPower

def marginCatalog (z : List ℕ×List ℕ) : List (ℕ×ℕ) :=
  smallCellCatalog (z,marginThreshold z)

def marginCatalogRealizer : Realizer marginCatalog :=
  composition (pair identity marginThresholdRealizer) smallCellCatalogRealizer

theorem polynomial_marginCatalog : PolynomialTime marginCatalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_marginThreshold)
    polynomial_smallCellCatalog

abbrev RawProfileInput := (List ℕ×List ℕ)×(List ℕ×List ℕ)

def prepareProfileInput (z : RawProfileInput) : ProfileCheckData :=
  (((marginCatalog z.1,z.2),z.1),marginThreshold z.1)

def prepareProfileInputRealizer : Realizer prepareProfileInput :=
  pair (pair (pair (composition (f := fun z : RawProfileInput => z.1) (g := marginCatalog) first marginCatalogRealizer) second) first)
    (composition (f := fun z : RawProfileInput => z.1) (g := marginThreshold) first marginThresholdRealizer)

theorem polynomial_prepareProfileInput : PolynomialTime prepareProfileInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_marginCatalog) polynomial_second)
    polynomial_first) (polynomial_composition polynomial_first polynomial_marginThreshold)

def preparedProposal (z : RawProfileInput×List Bool) : Option (List ℕ×List ℕ) :=
  codeNeighborProposal (prepareProfileInput z.1,z.2)

def preparedProposalRealizer : Realizer preparedProposal :=
  composition (f := fun z : RawProfileInput×List Bool => (prepareProfileInput z.1,z.2))
    (g := codeNeighborProposal)
    (pair (composition (f := fun z : RawProfileInput×List Bool => z.1)
      (g := prepareProfileInput) first prepareProfileInputRealizer) second) codeNeighborProposalRealizer

/-- A single binary program computes the threshold, small-cell catalog,
full neighbor list, and indexed proposal from the supplied margins. -/
theorem polynomial_preparedProposal : PolynomialTime preparedProposalRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_prepareProfileInput) polynomial_second)
    polynomial_codeNeighborProposal

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma marginThreshold_ofFn :
    marginThreshold (List.ofFn r,List.ofFn c)=
      (dimensionAllowance (I := Fin m) (J := Fin n))^20 := by
  simp only [marginThreshold,marginDimension,List.length_ofFn,dimensionAllowance,Fintype.card_fin]

lemma prepareProfileInput_eq (x : PaperStates r c) :
    prepareProfileInput ((List.ofFn r,List.ofFn c),stateCode r c (computedCellEquiv r c) x)=
      stateCodeData r c (computedCellEquiv r c) x := by
  unfold prepareProfileInput stateCodeData codeCheckData
  rw [computedCellEquiv_catalog]
  simp only [marginCatalog,marginThreshold_ofFn,computedCatalog]

theorem preparedProposal_eq (x : PaperStates r c)
    (bits : Fin (smallProposalBits (I := Fin m) (J := Fin n)) → Bool) :
    (preparedProposal (((List.ofFn r,List.ofFn c),stateCode r c (computedCellEquiv r c) x),
      List.ofFn bits)).bind (decodeStateCode r c (computedCellEquiv r c))=
        decodedCodeProposal r c (computedCellEquiv r c) x bits := by
  have hi := prepareProfileInput_eq r c x
  have hp := congrArg (fun z => codeNeighborProposal (z,List.ofFn bits)) hi
  have hb := congrArg (fun z => z.bind (decodeStateCode r c (computedCellEquiv r c))) hp
  have hd := @decodedCodeProposal_apply m n (computedCatalog r c).length r c
    (computedCellEquiv r c) x bits
  simpa only [preparedProposal] using hb.trans hd.symm

end
end ContingencyTables.SmallGraphProfiles

end OAI
