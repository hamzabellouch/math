import OAI.Combinatorics.ContingencyTables.Transport.CanonicalIntegerLaw

namespace OAI

/-! # Explicit table weights from the computed dense-law cache -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

abbrev CompletionCache := CanonicalParameters×List ℕ

def cachedCompletionWeight (z : CompletionCache×Option MatrixCode) : ℕ :=
  z.2.elim 0 (fun X => z.1.2.getD (canonicalTableIndex (z.1.1,X)) 0)

def cachedCompletionWeightRealizer : Realizer cachedCompletionWeight := by
  let context : Realizer (fun z : CompletionCache×MatrixCode => z.1.1) :=
    composition first first
  let cache : Realizer (fun z : CompletionCache×MatrixCode => z.1.2) :=
    composition first second
  let index := composition (pair context second) canonicalTableIndexRealizer
  let entry := composition (pair cache index) (getDFast 0)
  exact optionCases (constant 0) entry

lemma polynomial_cachedCompletionWeight : PolynomialTime cachedCompletionWeightRealizer := by
  unfold cachedCompletionWeightRealizer
  exact polynomial_optionCases (polynomial_constant 0)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        polynomial_canonicalTableIndex)) (polynomial_getDFast 0))

def completionWeightEntry (z : CompletionCache×Option MatrixCode) : Option MatrixCode×ℕ :=
  (z.2,cachedCompletionWeight z)

def completionWeightEntryRealizer : Realizer completionWeightEntry :=
  pair second cachedCompletionWeightRealizer

lemma polynomial_completionWeightEntry : PolynomialTime completionWeightEntryRealizer :=
  polynomial_pair polynomial_second polynomial_cachedCompletionWeight

def completionWeightInput (z : CanonicalParameters) : CompletionCache×List (Option MatrixCode) :=
  ((z,canonicalDrawCounts z),completionCandidates z.1)

def completionWeightInputRealizer : Realizer completionWeightInput :=
  pair (pair identity canonicalDrawCountsRealizer)
    (composition first completionCandidatesRealizer)

def completionWeightMeasure (z : CanonicalParameters) : ℕ :=
  canonicalTabulationMeasure z+completionEnumerationMeasure z.1

private lemma weight_le_completionMeasure (z : CanonicalParameters) :
    weight z≤completionWeightMeasure z := by
  unfold completionWeightMeasure canonicalTabulationMeasure
  omega

lemma work_completionWeightInput :
    WorkBound completionWeightInputRealizer completionWeightMeasure := by
  have hw : WorkBound canonicalDrawCountsRealizer completionWeightMeasure :=
    work_remeasure work_canonicalDrawCounts Polynomial.X (fun z => by
      simp only [Polynomial.eval_X,completionWeightMeasure]; omega)
  have he : WorkBound (composition first completionCandidatesRealizer) completionWeightMeasure := by
    apply work_composition (work_of_polynomial polynomial_first Polynomial.X
      (fun z => by simpa using weight_le_completionMeasure z)) work_completionCandidates Polynomial.X
    intro z
    simp only [Polynomial.eval_X,completionWeightMeasure]
    omega
  have hi : WorkBound (identity (A := CanonicalParameters)) completionWeightMeasure :=
    work_of_polynomial polynomial_identity Polynomial.X
      (fun z => by simpa using weight_le_completionMeasure z)
  unfold completionWeightInputRealizer
  apply work_pair _ he Polynomial.X (fun z => by simpa using weight_le_completionMeasure z)
  exact work_pair hi hw Polynomial.X (fun z => by simpa using weight_le_completionMeasure z)

def completionWeights (z : CanonicalParameters) : List (Option MatrixCode×ℕ) :=
  (completionCandidates z.1).map
    (fun o => (o,cachedCompletionWeight ((z,canonicalDrawCounts z),o)))

def completionWeightsRealizer : Realizer completionWeights :=
  composition completionWeightInputRealizer (mapWith completionWeightEntryRealizer)

section
attribute [local irreducible] completionWeightInputRealizer

theorem work_completionWeights : WorkBound completionWeightsRealizer completionWeightMeasure := by
  unfold completionWeightsRealizer
  exact work_then_polynomial work_completionWeightInput
    (polynomial_mapWith polynomial_completionWeightEntry)
end

attribute [local irreducible] canonicalDrawCounts canonicalCounts

lemma cachedCompletionWeight_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (o : Option (Table R P)) :
    cachedCompletionWeight ((((marginCode R,marginCode P),(d,h)),
      canonicalDrawCounts ((marginCode R,marginCode P),(d,h))),o.map tableOutput)=
      o.elim 0 (fun X => (canonicalCounts R P hd hR hP htotal h).count X) := by
  cases o with
  | none => rfl
  | some X => exact canonicalCounts_computed R P hd hR hP htotal h hq X

/-- The explicit list contains every feasible table once. Each rejected
free vector has zero weight; the surviving weights are the actual draw counts. -/
theorem completionWeights_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ) :
    completionWeights ((marginCode R,marginCode P),(d,h))=
      List.ofFn (fun k : Fin (((∑ i,R i)+1)^(m*n)) =>
        let o := BoxCompletion.decode R P htotal (∑ i,R i) (finFunctionFinEquiv.symm k)
        (o.map tableOutput,o.elim 0 (fun X => (canonicalCounts R P hd hR hP htotal h).count X))) := by
  unfold completionWeights
  rw [completionCandidates_code R P htotal,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  dsimp only [Function.comp_apply]
  congr 1
  exact cachedCompletionWeight_actual R P hd hq hR hP htotal h _

end ContingencyTables.DensePrograms

end OAI
