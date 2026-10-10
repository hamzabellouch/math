import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperCodeNeighbors
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperLocalProposal

namespace OAI

/-! # The compiled neighbor draw has the small-chain proposal law -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def codeNeighborProposal (z : ProfileCheckData×List Bool) : Option (List ℕ×List ℕ) :=
  listWordChoice (codeNeighbors z.1,z.2)

def codeNeighborProposalRealizer : Realizer codeNeighborProposal :=
  composition (pair (composition
    (f := fun z : ProfileCheckData×List Bool => z.1) (g := codeNeighbors)
    first codeNeighborsRealizer) second) listWordChoiceRealizer

theorem polynomial_codeNeighborProposal : PolynomialTime codeNeighborProposalRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_codeNeighbors) polynomial_second)
    polynomial_listWordChoice

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts FirstSuccess FairBits

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "small" => paperSmall r c
local notation "B" => stateCapacity r c
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "L" => d^12
local notation "U" => d^20
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

def stateCode (x : PaperStates r c) : List ℕ×List ℕ :=
  profileCode small e (physicalProfile small B r c L x)

def stateCodeData (x : PaperStates r c) : ProfileCheckData :=
  codeCheckData (cellCatalog small e) (List.ofFn r) (List.ofFn c) U (stateCode r c e x)

def decodeStateCode (v : List ℕ×List ℕ) : Option (PaperStates r c) :=
  if v.1.length=q ∧ v.2.length=q then decodeProfile r c (profileOfCode small e v) else none

lemma decode_stateCode (x : PaperStates r c) :
    decodeStateCode r c e (stateCode r c e x)=some x := by
  unfold decodeStateCode stateCode
  rw [ite_eq_left (by simp only [profileCode,viewList,List.length_ofFn,and_self]),profileOfCode_code]
  exact (decodeProfile_eq_some_iff r c _ x).mpr rfl

lemma stateCode_injective : Function.Injective (stateCode r c e) := by
  intro x y h
  have he := congrArg (decodeStateCode r c e) h
  rw [decode_stateCode,decode_stateCode] at he
  exact Option.some.inj he

theorem decodeStateCode_eq_some_iff (v : List ℕ×List ℕ) (x : PaperStates r c) :
    decodeStateCode r c e v=some x ↔ stateCode r c e x=v := by
  constructor
  · intro h
    unfold decodeStateCode at h
    split_ifs at h with hlen
    have hx := (decodeProfile_eq_some_iff r c _ x).mp h
    exact (congrArg (profileCode small e) hx).trans (profileCode_ofCode small e v hlen.1 hlen.2)
  · rintro rfl
    exact decode_stateCode r c e x

def codeNeighborStates (x : PaperStates r c) : List (PaperStates r c) :=
  (codeNeighbors (stateCodeData r c e x)).filterMap (decodeStateCode r c e)

lemma codeNeighborStates_nodup (x : PaperStates r c) : (codeNeighborStates r c e x).Nodup := by
  apply List.Nodup.filterMap
  · intro a b y ha hb
    exact ((decodeStateCode_eq_some_iff r c e a y).mp ha).symm.trans
      ((decodeStateCode_eq_some_iff r c e b y).mp hb)
  · exact codeNeighbors_nodup _

theorem mem_codeNeighborStates (htotal : (∑ i,r i)=∑ j,c j) (x y : PaperStates r c) :
    y∈codeNeighborStates r c e x ↔ physicalAdjacent r c U L B (stateCapacity_small r c) x y := by
  simp only [codeNeighborStates,List.mem_filterMap]
  constructor
  · rintro ⟨v,hv,hy⟩
    have he := (decodeStateCode_eq_some_iff r c e v y).mp hy
    rw [←he] at hv
    exact (mem_codeNeighbors r c htotal e x y).mp hv
  · intro h
    exact ⟨stateCode r c e y,(mem_codeNeighbors r c htotal e x y).mpr h,decode_stateCode r c e y⟩

lemma codeNeighborStates_length (x : PaperStates r c) :
    (codeNeighborStates r c e x).length≤6*d^2 := by
  have hq : q≤d := by
    calc
      q = Fintype.card (Cells small) := by simpa only [Fintype.card_fin] using Fintype.card_congr e
      _ ≤ Fintype.card (Fin m×Fin n) := Fintype.card_subtype_le _
      _ ≤ d := by simpa only [Fintype.card_prod] using (dimension_le_allowance (I := Fin m) (J := Fin n))
  have hc : (codeNeighbors (stateCodeData r c e x)).length≤6*q^2 :=
    codeNeighbors_length _ q (by simp [stateCodeData,codeCheckData,stateCode,profileCode,viewList])
      (by simp [stateCodeData,codeCheckData,stateCode,profileCode,viewList])
  exact (List.length_filterMap_le _ _).trans (hc.trans (by gcongr))

lemma codeNeighborStates_codes (x : PaperStates r c) :
    (codeNeighborStates r c e x).length≤2^s := by
  calc
    _ ≤ 6*d^2 := codeNeighborStates_length r c e x
    _ ≤ 32*d^2 := Nat.mul_le_mul_right _ (by decide)
    _ ≤ 2^s := Nat.le_pow_clog (by decide) _

lemma codeNeighbors_decode_total (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) :
    ∀ v∈codeNeighbors (stateCodeData r c e x),∃ y,decodeStateCode r c e v=some y := by
  intro v hv
  have hp := (List.mem_filter.mp (List.mem_dedup.mp hv)).2
  obtain ⟨y,hy⟩ := (profileTest_code_iff r c htotal e v).mp hp
  exact ⟨y,(decodeStateCode_eq_some_iff r c e v y).mpr hy⟩

private lemma getElem_filterMap_total {A C : Type*} (f : A → Option C) (xs : List A)
    (h : ∀ a∈xs,∃ b,f a=some b) (i : ℕ) :
    (xs[i]?).bind f=(xs.filterMap f)[i]? := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨b,hb⟩ := h a (by simp)
    have ht : ∀ a∈xs,∃ b,f a=some b := fun a ha => h a (by simp [ha])
    cases i with
    | zero => simp [hb]
    | succ i => simpa only [List.getElem?_cons_succ,List.filterMap_cons,hb] using ih ht i

def decodedCodeProposal (x : PaperStates r c) (bits : Fin s → Bool) : Option (PaperStates r c) :=
  (codeNeighborProposal (stateCodeData r c e x,List.ofFn bits)).bind (decodeStateCode r c e)

lemma decodedCodeProposal_apply (x : PaperStates r c) (bits : Fin s → Bool) :
    decodedCodeProposal r c e x bits=
      (codeNeighborProposal (stateCodeData r c e x,List.ofFn bits)).bind (decodeStateCode r c e) := rfl

lemma decodedCodeProposal_eq (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c)
    (bits : Fin s → Bool) :
    decodedCodeProposal r c e x bits=listBitDraw (codeNeighborStates r c e x) s bits := by
  unfold decodedCodeProposal codeNeighborProposal
  rw [listWordChoice_ofFn]
  exact getElem_filterMap_total (decodeStateCode r c e) _
    (codeNeighbors_decode_total r c e htotal x) _

/-- The implemented binary neighbor choice has exactly the proposal
law used by the already-proved small-chain mixing estimate. -/
theorem decodedCodeProposal_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin s → Bool)) (decodedCodeProposal r c e x)=smallProposalLaw r c x := by
  have he : decodedCodeProposal r c e x=listBitDraw (codeNeighborStates r c e x) s := by
    funext bits
    exact decodedCodeProposal_eq r c e htotal x bits
  rw [he]
  apply law_ext_except _ _ none
  intro y hy
  cases y with
  | none => exact False.elim (hy rfl)
  | some y =>
    rw [listBitDraw_mass_decidableEq (inferInstance : DecidableEq (Option (PaperStates r c)))
      _ (codeNeighborStates_nodup r c e x) s (codeNeighborStates_codes r c e x) y,
      smallProposalLaw_mass_some]
    unfold proposalWeights
    by_cases hxy : physicalAdjacent r c U L B (stateCapacity_small r c) x y
    · have hy := (mem_codeNeighborStates r c e htotal x y).mpr hxy
      simp only [ite_eq_left hy,ite_eq_left hxy,smallProposalRat]
    · have hy := mt (mem_codeNeighborStates r c e htotal x y).mp hxy
      simp only [ite_eq_right hy,ite_eq_right hxy]

end
end ContingencyTables.SmallGraphProfiles

end OAI
