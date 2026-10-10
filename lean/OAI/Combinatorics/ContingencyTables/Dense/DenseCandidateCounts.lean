import OAI.Combinatorics.ContingencyTables.Machines.CompletionEnumerationProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseTrialCountProgram

namespace OAI

/-! # Exact accepted counts throughout the enumerated completion box -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

abbrev TrialCountContext := (List ℕ×List Bool)×CanonicalParameters

def candidateCountInput (z : TrialCountContext×MatrixCode) : TrialCountData :=
  (z.1.1,(((z.1.2.1,z.2),z.1.2.2.1),z.1.2.2.2))

def candidateCountInputRealizer : Realizer candidateCountInput :=
  pair (composition first first)
    (pair (pair (pair (composition (composition first second) first) second)
      (composition (composition (composition first second) second) first))
      (composition (composition (composition first second) second) second))

lemma polynomial_candidateCountInput : PolynomialTime candidateCountInputRealizer := by
  unfold candidateCountInputRealizer
  exact polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first) polynomial_second)
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_first))
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_second))

def candidateCount (z : TrialCountContext×Option MatrixCode) : ℕ :=
  z.2.elim 0 (fun X => trialTableCount (candidateCountInput (z.1,X)))

def candidateCountRealizer : Realizer candidateCount :=
  optionCases (constant 0) (composition candidateCountInputRealizer trialTableCountRealizer)

lemma polynomial_candidateCount : PolynomialTime candidateCountRealizer :=
  polynomial_optionCases (polynomial_constant 0)
    (polynomial_composition polynomial_candidateCountInput polynomial_trialTableCount)

def candidateCounts (z : TrialCountContext) : List ℕ :=
  (completionCandidates z.2.1).map (fun o => candidateCount (z,o))

def candidateCountsRealizer : Realizer candidateCounts :=
  composition (pair identity
    (composition (composition second first) completionCandidatesRealizer))
    (mapWith candidateCountRealizer)

def candidateCountMeasure (z : TrialCountContext) : ℕ :=
  gridStateCount (completionEnumerationData z.2.1)+weight z

/-- Work is polynomial in the number of candidate free vectors and the
cached walk vector; no random tapes are enumerated. -/
theorem work_candidateCounts : WorkBound candidateCountsRealizer candidateCountMeasure := by
  have hm : WorkBound (composition (second (A := List ℕ×List Bool)
      (B := CanonicalParameters)) first) candidateCountMeasure :=
    work_of_polynomial (polynomial_composition polynomial_second polynomial_first)
      Polynomial.X (fun z => by simp only [candidateCountMeasure,Polynomial.eval_X]; omega)
  obtain ⟨p,hp⟩ := hm
  have he : WorkBound (composition (composition second first) completionCandidatesRealizer)
      candidateCountMeasure := by
    apply work_composition ⟨p,hp⟩ work_completionCandidates (Polynomial.X+p)
    intro z
    have hw := hp z
    simp only [completionEnumerationMeasure,candidateCountMeasure,
      Polynomial.eval_add,Polynomial.eval_X]
    change _≤p.eval (candidateCountMeasure z) at hw
    unfold candidateCountMeasure at hw
    dsimp only [Function.comp_apply] at hw ⊢
    omega
  unfold candidateCountsRealizer
  apply work_then_polynomial _ (polynomial_mapWith polynomial_candidateCount)
  exact work_pair (work_of_polynomial polynomial_identity Polynomial.X (fun z => by
    simp only [candidateCountMeasure,Polynomial.eval_X]; omega)) he Polynomial.X
    (fun z => by simp only [candidateCountMeasure,Polynomial.eval_X]; omega)

theorem candidateCount_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (h : ℕ) (cap : List Bool)
    (hcap : ∀ j : Fin (m*n),FairBits.offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d≤cap.length)
    (o : Option (Table R P)) :
    candidateCount
      (((tabulateDenseWalk ((marginCode R,marginCode P),(d,h)),cap),
        ((marginCode R,marginCode P),(d,h))),o.map tableOutput)=
      o.elim 0 (fun X => (denseTrialCounts R P d hd hR hP finProdFinEquiv h
        (canonicalOrigin (m*n) d (by omega))).count
          (tableTrial R P d hd hR hP finProdFinEquiv X)) := by
  cases o with
  | none => rfl
  | some X => exact trialTableCount_actual R P hd hq hR hP h cap hcap X

/-- The sum of all enumerated successful counts is exactly the accepted
mass numerator. Rejected integer completions contribute zero. -/
theorem candidateCounts_sum {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (cap : List Bool)
    (hcap : ∀ j : Fin (m*n),FairBits.offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d≤cap.length) :
    (candidateCounts ((tabulateDenseWalk ((marginCode R,marginCode P),(d,h)),cap),
      ((marginCode R,marginCode P),(d,h)))).sum=
      ∑ X : Table R P,(denseTrialCounts R P d hd hR hP finProdFinEquiv h
        (canonicalOrigin (m*n) d (by omega))).count
          (tableTrial R P d hd hR hP finProdFinEquiv X) := by
  unfold candidateCounts
  rw [completionCandidates_code R P htotal,List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply]
  simp_rw [candidateCount_actual R P hd hq hR hP h cap hcap]
  let w : Table R P → ℕ := fun X =>
    (denseTrialCounts R P d hd hR hP finProdFinEquiv h
      (canonicalOrigin (m*n) d (by omega))).count
        (tableTrial R P d hd hR hP finProdFinEquiv X)
  have hs := (finFunctionFinEquiv : BoxCompletion.Box m n (∑ i,R i) ≃
      Fin (((∑ i,R i)+1)^(m*n))).symm.sum_comp
    (fun z => (BoxCompletion.decode R P htotal (∑ i,R i) z).elim 0 w)
  exact hs.trans (BoxCompletion.sum_decode R P htotal (le_refl _) w)

/-- The computed subtraction includes every rejected completion and
every unused dyadic slot in the actual dense trial. -/
theorem candidateCounts_failure {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (cap : List Bool)
    (hcap : ∀ j : Fin (m*n),FairBits.offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d≤cap.length) :
    2^denseTrialBits R P d finProdFinEquiv h-
      (candidateCounts ((tabulateDenseWalk ((marginCode R,marginCode P),(d,h)),cap),
        ((marginCode R,marginCode P),(d,h)))).sum=
    ((denseTrialCounts R P d hd hR hP finProdFinEquiv h
      (canonicalOrigin (m*n) d (by omega))).push
        (trialSuccess R P d finProdFinEquiv htotal)).count none := by
  rw [candidateCounts_sum R P hd hq hR hP htotal h cap hcap]
  exact (denseTrial_failure_count R P d hd hR hP finProdFinEquiv htotal h
    (canonicalOrigin (m*n) d (by omega))).symm

end ContingencyTables.DensePrograms

end OAI
