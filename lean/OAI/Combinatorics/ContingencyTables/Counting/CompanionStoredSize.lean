import OAI.Combinatorics.ContingencyTables.Counting.CompanionFractionSize

namespace OAI

/-! # A phase adds a bounded amount to each stored fraction's binary height -/
namespace ContingencyTables.CompanionStoredSize
open MatchingFPRAS CompanionFractionSize CompanionMultiplierMatrixProgram
open CompanionPhaseFinishProgram CompanionMultiplierProgram CompanionPhaseCounts

private lemma getD_property {X : Type} (P : X→Prop) (xs : List X) (i : ℕ) (d : X)
    (hx : ∀ x∈xs,P x) (hd : P d) : P (xs.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases he : xs[i]? with
  | none => exact hd
  | some x => exact hx x (List.mem_of_getElem? he)

def MatrixHeight (M : ℕ) (w : FractionMatrix) : Prop :=
  ∀ row∈w,∀ x∈row,TreeFraction.height x ≤ M

def StoredHeight (M : ℕ) (s : Stored) : Prop := MatrixHeight M s.1 ∧ TreeFraction.height s.2 ≤ M

lemma readEntry_height (M : ℕ) (hM : 1 ≤ M) (w : FractionMatrix) (hw : MatrixHeight M w)
    (ij : ℕ×ℕ) : TreeFraction.height (readEntry (w,ij)) ≤ M := by
  have hr : ∀ x∈w.getD ij.1 [],TreeFraction.height x ≤ M :=
    getD_property (fun row => ∀ x∈row,TreeFraction.height x ≤ M) w ij.1 [] hw
      (by simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true])
  exact getD_property (fun x => TreeFraction.height x ≤ M) _ ij.2 (0,1) hr
    (by simpa only [TreeFraction.height,Nat.size_zero,Nat.size_one,Nat.zero_max] using hM)

lemma updateMatrix_height (M : ℕ) (hM : 1 ≤ M) (z : CompanionMultiplierMatrixProgram.Input)
    (hw : MatrixHeight M z.2) : MatrixHeight (M+z.1.2.length+1) (updateMatrix z) := by
  intro row hr x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  change TreeFraction.height (updateCode ((z.1,(i,j)),readEntry (z.2,(i,j)))) ≤ _
  exact (updateCode_height _).trans (by
    have h := readEntry_height M hM z.2 hw (i,j)
    dsimp only
    omega)

lemma terms_length (z : CompanionPhaseFinishProgram.Input) :
    (terms z).length=(trajectory z).2.length := by
  simp only [terms,CompanionPhaseFinishProgram.indices,List.length_map,List.length_range]

lemma terms_height (z : CompanionPhaseFinishProgram.Input) (V : ℕ) (hV : 1 ≤ V)
    (hv : ∀ x∈z.2,TreeFraction.height x.1 ≤ V ∧ TreeFraction.height x.2 ≤ V) :
    ∀ x∈terms z,TreeFraction.height x ≤ 2*V+1 := by
  intro x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  have hb := getD_property
    (fun x : TreeFraction.Fraction×TreeFraction.Fraction =>
      TreeFraction.height x.1 ≤ V ∧ TreeFraction.height x.2 ≤ V)
    z.2 i ((0,1),(0,1)) hv (by
      simpa only [TreeFraction.height,Nat.size_zero,Nat.size_one,Nat.zero_max,and_self] using hV)
  exact term_height (termInput (z,i)) V hb.1 hb.2

lemma ratio_height (z : CompanionPhaseFinishProgram.Input) (V : ℕ) (hV : 1 ≤ V)
    (hv : ∀ x∈z.2,TreeFraction.height x.1 ≤ V ∧ TreeFraction.height x.2 ≤ V) :
    TreeFraction.height (ratio z) ≤ (trajectory z).2.length*(2*V+3)+(trajectory z).2.length+3 := by
  have ht := sum_height (terms z) (2*V+1) (terms_height z V hV hv)
  rw [terms_length] at ht
  have hconst : 2*V+1+2=2*V+3 := by omega
  rw [hconst] at ht
  have hc : TreeFraction.height (count z) ≤ (trajectory z).2.length+1 := by
    have hp : plainCountCode (trajectory z) ≤ (trajectory z).2.length := List.length_filter_le _ _
    have hs : (plainCountCode (trajectory z)).size ≤ plainCountCode (trajectory z) :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    change max (plainCountCode (trajectory z)).size (1:ℕ).size ≤ _
    norm_num only [Nat.size_one]
    omega
  have hr := height_div (total z) (count z)
  change TreeFraction.height (ratio z) ≤ _ at hr
  change TreeFraction.height (total z) ≤ _ at ht
  omega

/-- This bound is additive in the old stored height; iterating phases
therefore preserves a polynomial representation size. -/
lemma next_height (z : CompanionPhaseFinishProgram.Input) (M V : ℕ) (hM : 1 ≤ M) (hV : 1 ≤ V)
    (hw : MatrixHeight M z.1.1.2) (he : TreeFraction.height z.1.2 ≤ M)
    (hv : ∀ x∈z.2,TreeFraction.height x.1 ≤ V ∧ TreeFraction.height x.2 ≤ V) :
    StoredHeight (M+(trajectory z).2.length*(2*V+3)+(trajectory z).2.length+5) (next z) := by
  constructor
  · have hm := updateMatrix_height M hM z.1.1 hw
    intro row hr x hx
    have h := hm row hr x hx
    change TreeFraction.height x ≤ M+(trajectory z).2.length+1 at h
    omega
  · have hr := ratio_height z V hV hv
    have hm := height_mul z.1.2 (ratio z)
    change TreeFraction.height (estimate z) ≤ _ at hm
    change TreeFraction.height (estimate z) ≤ _
    omega

end ContingencyTables.CompanionStoredSize

end OAI
