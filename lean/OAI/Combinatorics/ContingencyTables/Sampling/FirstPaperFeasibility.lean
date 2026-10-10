import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalOriginalResiduals
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperInitialization

namespace OAI

/-! # Arithmetic tests for the positive small-profile state space

Feasibility is decided by coordinate bounds, the allowed local pattern,
and residual margin equations. No completion count is evaluated.
-/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open PhysicalCompletionFibres SmallContextFibres FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions FirstPaperProfiles

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
omit [LinearOrder I] [LinearOrder J] in
/-- Equal residual totals and zero margins outside a rectangle suffice
for a supported completion, including empty row or column types. -/
lemma supported_completion_nonempty (small : I → J → Bool)
    (p : I → Prop) (q : J → Prop)
    (hrect : ∀ i j,small i j=false ↔ p i ∧ q j)
    (R : I → ℕ) (C : J → ℕ) (ht : (∑ i,R i)=∑ j,C j)
    (hR : ∀ i,¬p i → R i=0) (hC : ∀ j,¬q j → C j=0) :
    Nonempty (LargeCompletion small R C) := by
  obtain ⟨A⟩ : Nonempty (Table R C) := ⟨GreedyFeasibleTable.reindexed R C ht⟩
  refine ⟨⟨A,?_⟩⟩
  intro i j hs
  by_cases hi : p i
  · have hj : ¬q j := by
      intro hj
      exact Bool.noConfusion (hs.symm.trans ((hrect i j).mpr ⟨hi,hj⟩))
    have he : A.val i j ≤ C j := by
      rw [←A.property.2 j]
      exact Finset.single_le_sum (f := fun k => A.val k j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Nat.eq_zero_of_le_zero (he.trans_eq (hC j hj))
  · have he : A.val i j ≤ R i := by
      rw [←A.property.1 i]
      exact Finset.single_le_sum (f := fun k => A.val i k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact Nat.eq_zero_of_le_zero (he.trans_eq (hR i hi))

variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "U" => d^20
local notation "L" => d^12
local notation "small" => paperSmall r c
local notation "B" => stateCapacity r c

/-- Padded residual margins can be computed before establishing feasibility. -/
def profileRows (z : SmallProfile small) (i : I) : ℕ :=
  r i-smallRow small (smallView small z false) i+rowLargeCount small i*L

def profileColumns (z : SmallProfile small) (j : J) : ℕ :=
  c j-smallColumn small B (smallView small z true) j+columnLargeCount small j*L

/-- Each field is a finite integer test on the candidate profile. -/
structure ProfileFeasible (z : SmallProfile small) : Prop where
  bounded : ∀ a,z a ≤ B a.1.val.1 a.1.val.2
  pattern : Pattern small B z
  residuals : OriginalResidualsNonnegative small B (smallView small z false) (smallView small z true) r c
  rows_outside : ∀ i,¬U ≤ r i → profileRows r c z i=0
  columns_outside : ∀ j,¬U ≤ c j → profileColumns r c z j=0
  totals : (∑ i,profileRows r c z i)=∑ j,profileColumns r c z j

omit [LinearOrder I] [LinearOrder J] in
lemma profile_capacity (z : SmallProfile small) :
    ∀ i j,small i j=false → (∑ k,profileRows r c z k) ≤ B i j :=
  paper_capacity_excludes_none small (smallView small z false) r d L U dimension_le_allowance

lemma physicalProfile_feasible (x : PaperStates r c) :
    ProfileFeasible r c (physicalProfile small B r c L x) := by
  have hcap := profile_capacity r c (physicalProfile small B r c L x)
  exact ⟨naturalProfile_bounded x.val.val,x.val.property,
    physical_original_residuals small B r c L x hcap,
    physical_residual_row_zero r c U L B x hcap,
    physical_residual_column_zero r c U L B x hcap,
    physical_residual_totals small B r c L x hcap⟩

/-- A passing arithmetic test constructs a completion by the greedy
rectangle algorithm, proving that its weight is strictly positive. -/
lemma profileFeasible_positive (z : SmallProfile small) (h : ProfileFeasible r c z) :
    0 < hardMarginal small B r c L z := by
  have hne := supported_completion_nonempty small
    (fun i => U ≤ r i) (fun j => U ≤ c j) (firstPaperSmall_false_iff r c U)
    (profileRows r c z) (profileColumns r c z) h.totals h.rows_outside h.columns_outside
  have hc := hardMarginal_eq_completionCount small B r c L z h.bounded (profile_capacity r c z)
  rw [ite_eq_left h.residuals] at hc
  rw [hc]
  exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hne)

/-- The successful integer tests recover an actual state without
searching the completion space. -/
def stateOfFeasible (z : SmallProfile small) (h : ProfileFeasible r c z) : PaperStates r c :=
  ⟨⟨(fun a => ⟨z a,Nat.lt_succ_of_le (h.bounded a)⟩),h.pattern⟩,
    profileFeasible_positive r c z h⟩

lemma stateOfFeasible_profile (z : SmallProfile small) (h : ProfileFeasible r c z) :
    physicalProfile small B r c L (stateOfFeasible r c z h)=z := rfl

/-- This is the complete test for membership in the chain's state space. -/
theorem profileFeasible_iff (z : SmallProfile small) :
    ProfileFeasible r c z ↔ ∃ x : PaperStates r c,physicalProfile small B r c L x=z := by
  constructor
  · intro h
    exact ⟨stateOfFeasible r c z h,rfl⟩
  · rintro ⟨x,rfl⟩
    exact physicalProfile_feasible r c x

/-- Failed candidates are discarded. Passing candidates retain all
completion multiplicity through the original physical state type. -/
def decodeProfile (z : SmallProfile small) : Option (PaperStates r c) :=
  if h : ProfileFeasible r c z then some (stateOfFeasible r c z h) else none

lemma decodeProfile_eq_some_iff (z : SmallProfile small) (x : PaperStates r c) :
    decodeProfile r c z=some x ↔ physicalProfile small B r c L x=z := by
  constructor
  · intro hx
    unfold decodeProfile at hx
    split_ifs at hx with h
    · have he := Option.some.inj hx
      rw [←he]
      exact stateOfFeasible_profile r c z h
  · intro hx
    have h : ProfileFeasible r c z := hx ▸ physicalProfile_feasible r c x
    rw [decodeProfile,dite_eq_left h]
    congr 1
    apply physicalProfile_injective small B r c L
    exact (stateOfFeasible_profile r c z h).trans hx.symm

end
end ContingencyTables.SmallGraphProfiles

end OAI
