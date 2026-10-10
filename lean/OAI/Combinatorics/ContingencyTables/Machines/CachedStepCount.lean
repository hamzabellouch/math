import OAI.Combinatorics.ContingencyTables.Machines.CachedCompletionWeights
import OAI.Combinatorics.ContingencyTables.Machines.CachedDecisionSemantics
import OAI.Combinatorics.ContingencyTables.Transport.BooleanEnumeration
import OAI.Combinatorics.ContingencyTables.Transport.ListedIntegerLaw

namespace OAI

/-! # Weighted transitions from the cached completion list -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped BigOperators Classical

attribute [local irreducible] cachedDecisionRealizer cachedDecision

abbrev DecisionQuery := ShortStep×(List ℕ×List ℕ)

/-- A rejected box entry contributes zero. A valid completion contributes
its cached integer multiplicity precisely when it reaches the target. -/
def decisionWeight (z : DecisionQuery×(Option MatrixCode×ℕ)) : ℕ :=
  z.2.1.elim 0 (fun X => if cachedDecision (z.1.1,X)=z.1.2 then z.2.2 else 0)

def decisionWeightRealizer : Realizer decisionWeight := by
  let input : Realizer (fun z : DecisionQuery×(Option MatrixCode×ℕ) =>
      ((z.1,z.2.2),z.2.1)) := pair (pair first (composition second second))
        (composition second first)
  let step : Realizer (fun z : (DecisionQuery×ℕ)×MatrixCode =>
      (z.1.1.1,z.2)) := pair (composition (composition first first) first) second
  let target : Realizer (fun z : (DecisionQuery×ℕ)×MatrixCode => z.1.1.2) :=
    composition (composition first first) second
  let test := composition (pair (composition step cachedDecisionRealizer) target) profileCodeEqual
  let entry := choose test (composition first second) (constant 0)
  exact (composition input (optionCases (constant 0) entry)).congr (by
    intro z
    simp only [Function.comp_apply,decide_eq_true_eq]
    rfl)

lemma polynomial_decisionWeight : PolynomialTime decisionWeightRealizer := by
  unfold decisionWeightRealizer
  apply polynomial_congr
  exact polynomial_composition
    (polynomial_pair (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_second))
      (polynomial_composition polynomial_second polynomial_first))
    (polynomial_optionCases (polynomial_constant 0) (polynomial_choose
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_pair
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_first) polynomial_second) polynomial_cachedDecision)
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_second)) polynomial_profileCodeEqual)
      (polynomial_composition polynomial_first polynomial_second) (polynomial_constant 0)))

def decisionWeightSum (z : DecisionQuery×List (Option MatrixCode×ℕ)) : ℕ :=
  (z.2.map (fun a => decisionWeight (z.1,a))).sum

def decisionWeightSumRealizer : Realizer decisionWeightSum :=
  composition (mapWith decisionWeightRealizer) listSum

lemma polynomial_decisionWeightSum : PolynomialTime decisionWeightSumRealizer :=
  polynomial_composition (polynomial_mapWith polynomial_decisionWeight) polynomial_listSum

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.DensePrograms
open scoped BigOperators Classical
noncomputable section

/-- Free-box enumeration sums each feasible table's weight once. -/
lemma sum_completionWeights {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (w : MatrixCode → ℕ) :
    ((completionWeights ((marginCode R,marginCode P),(d,h))).map
      (fun z => z.1.elim 0 (fun X => z.2*w X))).sum=
      ∑ X : Table R P,(canonicalCounts R P hd hR hP htotal h).count X*w (tableOutput X) := by
  rw [completionWeights_actual R P hd hq hR hP htotal h,List.map_ofFn,List.sum_ofFn]
  let f : BoxCompletion.Box m n (∑ i,R i) → ℕ := fun z =>
    (BoxCompletion.decode R P htotal (∑ i,R i) z).elim 0
      (fun X => (canonicalCounts R P hd hR hP htotal h).count X*w (tableOutput X))
  have hs := finFunctionFinEquiv.symm.sum_comp f
  have hi : (∑ k : Fin (((∑ i,R i)+1)^(m*n)),
      let o := BoxCompletion.decode R P htotal (∑ i,R i) (finFunctionFinEquiv.symm k)
      (o.map tableOutput).elim 0 (fun X =>
        o.elim 0 (fun T => (canonicalCounts R P hd hR hP htotal h).count T)*w X))=
      ∑ z : BoxCompletion.Box m n (∑ i,R i),f z := by
    rw [←hs]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [f]
    cases BoxCompletion.decode R P htotal (∑ i,R i) (finFunctionFinEquiv.symm k) <;> rfl
  exact hi.trans (BoxCompletion.sum_decode R P htotal le_rfl _)

end
end ContingencyTables.DensePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] canonicalCounts completionWeights decisionWeightSum

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma decisionWeightSum_actual (htotal : ∑ i,r i=∑ j,c j) (h : ℕ)
    (x y : PaperStates r c) (word : Fin s → Bool) :
    decisionWeightSum ((encodedShortStep r c e h x word,stateCode r c e y),
      completionWeights ((marginCode (R x),marginCode (P x)),(d,h)))=
      ∑ A : Table (R x) (P x),if completionDecision R P x (decodedCodeProposal r c e x word) A=y
        then (canonicalCounts (R x) (P x) (listed_dimension_fourteen r c hr hc)
          (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
          (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
          (listed_paper_totals r c hr hc x) h).count A else 0 := by
  let w : MatrixCode → ℕ := fun X =>
    if cachedDecision (encodedShortStep r c e h x word,X)=stateCode r c e y then 1 else 0
  have he : decisionWeightSum ((encodedShortStep r c e h x word,stateCode r c e y),
      completionWeights ((marginCode (R x),marginCode (P x)),(d,h)))=
      ((completionWeights ((marginCode (R x),marginCode (P x)),(d,h))).map
        (fun z => z.1.elim 0 (fun X => z.2*w X))).sum := by
    unfold decisionWeightSum
    congr 1
    apply List.map_congr_left
    intro z _
    rcases z with ⟨o,a⟩
    cases o with
    | none => rfl
    | some X =>
      simp only [decisionWeight,Option.elim_some,w]
      split_ifs <;> simp
  rw [he,sum_completionWeights (R x) (P x) (listed_dimension_fourteen r c hr hc)
    (by simpa only [Fintype.card_prod,Fintype.card_fin] using (listed_dimensions r c hr hc).2.2)
    (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_paper_totals r c hr hc x) h w]
  apply Finset.sum_congr rfl
  intro A _
  simp only [w,cachedDecision_encoded r c e hr hc htotal h x word A,
    (stateCode_injective r c e).eq_iff]
  split_ifs <;> simp

end
end ContingencyTables.SmallGraphProfiles

end OAI
