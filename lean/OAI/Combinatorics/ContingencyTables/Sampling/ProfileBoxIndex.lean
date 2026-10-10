import OAI.Combinatorics.ContingencyTables.Transport.BoundedProfileSemantics
import OAI.Combinatorics.ContingencyTables.Dense.GridIndexProgram
import OAI.Combinatorics.ContingencyTables.Transport.BoxCompletion

namespace OAI

/-! # A computed finite-box index for the two small-profile views -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def profileBoxIndex (z : ProfileCheckData) : ℕ :=
  gridIndex (flattenViews z.1.1.2,z.2+1)

def profileBoxIndexRealizer : Realizer profileBoxIndex :=
  composition (pair (composition profileViews flattenViewsRealizer)
    (composition second successor)) gridIndexRealizer

lemma polynomial_profileBoxIndex : PolynomialTime profileBoxIndexRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_profileViews polynomial_flattenViews)
    (polynomial_composition polynomial_second polynomial_successor)) polynomial_gridIndex

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => d^20

abbrev ProfileBox := Fin (q+q) → Fin (U+1)
abbrev ProfileIndex := Fin ((U+1)^(q+q))

def profileBoxCoordinates (x : PaperStates r c) : ProfileBox (m := m) (n := n) (q := q) :=
  fun i => ⟨physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) x
      (flatViewEquiv (paperSmall r c) e i),
    Nat.lt_succ_of_le (stateCode_bounded r c x _ _)⟩

def profileIndex (x : PaperStates r c) : ProfileIndex (m := m) (n := n) (q := q) :=
  finFunctionFinEquiv (profileBoxCoordinates r c e x)

attribute [local irreducible] physicalProfile

lemma profileBoxCoordinates_code (x : PaperStates r c) :
    List.ofFn (fun i => (profileBoxCoordinates r c e x i).val)=
      flattenViews (stateCode r c e x) := by
  unfold profileBoxCoordinates stateCode
  exact (flatten_profileCode (paperSmall r c) e
    (physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) x)).symm

attribute [local irreducible] profileBoxCoordinates profileIndex

lemma profileBoxIndex_actual (x : PaperStates r c) :
    profileBoxIndex (stateCodeData r c e x)=(profileIndex r c e x).val := by
  unfold profileBoxIndex stateCodeData codeCheckData
  rw [←profileBoxCoordinates_code r c e x]
  unfold profileIndex
  exact gridIndex_ofFn _

def profileAt (k : ProfileIndex (m := m) (n := n) (q := q)) : Option (PaperStates r c) :=
  decodeStateCode r c e (splitViews (q,List.ofFn
    (fun i => ((finFunctionFinEquiv.symm k : ProfileBox (m := m) (n := n) (q := q)) i).val)))

lemma profileAt_index (x : PaperStates r c) :
    profileAt r c e (profileIndex r c e x)=some x := by
  unfold profileAt profileIndex
  rw [Equiv.symm_apply_apply,profileBoxCoordinates_code]
  have hl : (stateCode r c e x).1.length=q := by
    simp only [stateCode,profileCode,viewList,List.length_ofFn]
  have hs : splitViews (q,flattenViews (stateCode r c e x))=stateCode r c e x := by
    calc
      _=splitViews ((stateCode r c e x).1.length,flattenViews (stateCode r c e x)) :=
        congrArg (fun k => splitViews (k,flattenViews (stateCode r c e x))) hl.symm
      _=_ := split_flattenViews _
  rw [hs]
  exact decode_stateCode r c e x

lemma profileIndex_injective : Function.Injective (profileIndex r c e) := by
  intro x y hxy
  have h := congrArg (profileAt r c e) hxy
  simpa only [profileAt_index,Option.some.injEq] using h

lemma profileAt_eq_some (k : ProfileIndex (m := m) (n := n) (q := q))
    (x : PaperStates r c) : profileAt r c e k=some x ↔ profileIndex r c e x=k := by
  constructor
  · intro h
    have hc := (decodeStateCode_eq_some_iff r c e _ x).mp h
    have he : List.ofFn (fun i => (profileBoxCoordinates r c e x i).val)=
        List.ofFn (fun i => ((finFunctionFinEquiv.symm k :
          ProfileBox (m := m) (n := n) (q := q)) i).val) := by
      rw [profileBoxCoordinates_code]
      exact (congrArg flattenViews hc).trans (by simp [flattenViews,splitViews])
    have hv : profileBoxCoordinates r c e x=finFunctionFinEquiv.symm k := by
      funext i
      exact Fin.ext (congrFun (List.ofFn_injective he) i)
    unfold profileIndex
    rw [hv,Equiv.apply_symm_apply]
  · intro h
    rw [←h]
    exact profileAt_index r c e x

/-- The finite box includes every positive profile exactly once; all
other vectors contribute zero to a decoded weighted sum. -/
lemma sum_profileAt (w : PaperStates r c → ℕ) :
    (∑ k : ProfileIndex (m := m) (n := n) (q := q),(profileAt r c e k).elim 0 w)=
      ∑ x,w x := by
  simp_rw [BoxCompletion.decode_elim_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [profileAt_eq_some r c e]
  simp

end
end ContingencyTables.SmallGraphProfiles

end OAI
