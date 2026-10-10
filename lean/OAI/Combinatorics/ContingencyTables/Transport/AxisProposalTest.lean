import OAI.Combinatorics.ContingencyTables.Machines.NatListEquality
import OAI.Combinatorics.ContingencyTables.Dense.DenseAxisWordProgram

namespace OAI

/-! # Testing dense adjacency by the polynomial list of signed directions -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary

abbrev AxisNumberData := (ℕ×List ℕ)×ℕ

def axisNumberStep (z : AxisNumberData) : Option (List ℕ) :=
  axisListStep ((z.1,z.2/2),decide (z.2%2=1))

def axisNumberStepRealizer : Realizer axisNumberStep :=
  composition (pair (pair first (composition (pair second (constant 2)) quotient))
    (composition (pair (composition (pair second (constant 2)) remainder) (constant 1)) natEqual))
      axisListStepRealizer

theorem polynomial_axisNumberStep : PolynomialTime axisNumberStepRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair polynomial_first
      (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 2))
        polynomial_quotient))
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 2))
        polynomial_remainder) (polynomial_constant 1)) polynomial_natEqual)) polynomial_axisListStep

theorem axisNumberStep_eq {q K M : ℕ} (a : Grid (I := Fin q) K) (v : Fin M) :
    axisNumberStep ((K,gridNatCode a),v.val)=(axisCodeStep a v).map gridNatCode := by
  change axisListStep (((K,gridNatCode a),v.val/2),decide (v.val%2=1))=_
  by_cases hv : v.val<q*2
  · let u : Fin (q*2) := ⟨v.val,hv⟩
    let dir := (directionCodeEquiv q).symm u
    have hfirst : dir.1.val=v.val/2 := directionCode_first u
    have hsecond : dir.2=decide (v.val%2=1) := directionCode_second u
    rw [←hfirst,←hsecond,axisListStep_eq]
    simp only [axisCodeStep,dite_eq_left hv]
    rfl
  · have hi : ¬v.val/2<q := by omega
    have hlen : (gridNatCode a).length=q := by simp only [gridNatCode,List.length_ofFn]
    simp only [axisListStep,hlen,ite_eq_right hi,axisCodeStep,dite_eq_right hv,Option.map_none]

abbrev ProposalTestData := (ℕ×List ℕ)×List ℕ

def proposalMatches (z : ProposalTestData×ℕ) : Bool :=
  (axisNumberStep (z.1.1,z.2)).elim false (fun xs => NatListEquality.listEqual (xs,z.1.2))

def proposalMatchesRealizer : Realizer proposalMatches :=
  composition (pair identity
    (composition (pair (composition first first) second) axisNumberStepRealizer))
    (optionCases (constant false)
      (composition (pair second (composition (composition first first) second))
        NatListEquality.listEqualRealizer))

lemma polynomial_proposalMatches : PolynomialTime proposalMatchesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_axisNumberStep))
    (polynomial_optionCases (polynomial_constant false)
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_second)) NatListEquality.polynomial_listEqual))

def proposalIndices (z : ProposalTestData) : List ℕ := List.range (2*z.1.2.length)

def proposalIndicesRealizer : Realizer proposalIndices := by
  let L : Realizer (fun z : ProposalTestData => z.1.2.length) :=
    composition (composition first second) listLength
  let M := composition (pair (constant 2) L) multiply
  exact composition M range

lemma polynomial_proposalIndices : PolynomialTime proposalIndicesRealizer := by
  unfold proposalIndicesRealizer
  apply polynomial_boundedRange (polynomial_composition (polynomial_pair (polynomial_constant 2)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listLength)) polynomial_multiply) (2*Polynomial.X)
  intro z
  have hl: z.1.2.length ≤ weight z:=
    (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))
  simpa only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Function.comp_apply] using
    Nat.mul_le_mul_left 2 hl

def hasProposal (z : ProposalTestData) : Bool :=
  (proposalIndices z).any (fun i => proposalMatches (z,i))

def hasProposalRealizer : Realizer hasProposal :=
  (composition (composition (pair identity proposalIndicesRealizer)
    (mapWith proposalMatchesRealizer)) any).congr (by
      intro z
      simp only [Function.comp_apply,List.any_map,id_eq,Function.comp_def,hasProposal])

theorem polynomial_hasProposal : PolynomialTime hasProposalRealizer := by
  unfold hasProposalRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_proposalIndices)
    (polynomial_mapWith polynomial_proposalMatches)) polynomial_any

lemma gridNatCode_injective {q K : ℕ} : Function.Injective (gridNatCode (q := q) (K := K)) := by
  intro a b h
  have hv:=List.ofFn_injective h
  funext i
  apply Subtype.ext
  have hi:=congrFun hv i
  change (corner a i).toNat=(corner b i).toNat at hi
  have ha: 0≤corner a i := (a i).property.1
  have hb: 0≤corner b i := (b i).property.1
  change corner a i=corner b i
  have hv:=congrArg (fun n : ℕ => (n:ℤ)) hi
  simpa only [Int.toNat_of_nonneg ha,Int.toNat_of_nonneg hb] using hv

theorem hasProposal_code {q K : ℕ} (a b : Grid (I := Fin q) K) :
    hasProposal ((K,gridNatCode a),gridNatCode b)=true ↔ Neighbor a b := by
  simp only [hasProposal,List.any_eq_true]
  constructor
  · rintro ⟨v,hv,h⟩
    have hlen : v<2*q := by simpa [proposalIndices,gridNatCode] using hv
    rw [proposalMatches,axisNumberStep_eq a (⟨v,by omega⟩ : Fin (2*q))] at h
    cases he:axisCodeStep a (⟨v,by omega⟩ : Fin (2*q)) with
    | none => simp [he] at h
    | some c =>
      have hc : gridNatCode c=gridNatCode b :=
        (NatListEquality.listEqual_true _ _).mp (by simpa [he] using h)
      have hcb:=gridNatCode_injective hc
      subst c
      exact axisCodeStep_sound a b _ he
  · intro h
    obtain ⟨v,hv⟩:=axisCodeStep_exists (le_refl (q*2)) a b h
    refine ⟨v.val,?_,?_⟩
    · simpa only [proposalIndices,List.mem_range,gridNatCode,List.length_ofFn,Nat.mul_comm] using v.isLt
    · rw [proposalMatches,axisNumberStep_eq a v,hv]
      simpa only [Option.map_some,Option.elim_some] using
        (NatListEquality.listEqual_true _ _).mpr rfl

end ContingencyTables.DensePrograms

end OAI
