import OAI.Combinatorics.ContingencyTables.Machines.ScheduledCountInput
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalResidualVector

namespace OAI

/-! # Executing residual weights from margins, precision, and branch denominator -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] scheduledCounts residualVector originalCandidates originalCardinality

/-- Ordinary count vector, original margins, and reciprocal branch probability. -/
abbrev ScheduledResidualCache := List ℕ×(CompletionMargins×ℕ)

def scheduledResidualCache (z : SamplingParameters×ℕ) : ScheduledResidualCache :=
  (scheduledCounts z.1,(z.1.1,z.2))

def scheduledResidualCacheRealizer : Realizer scheduledResidualCache :=
  pair (composition (f := fun z : SamplingParameters×ℕ => z.1) (g := scheduledCounts)
    first scheduledCountsRealizer) (pair (composition first first) second)

def scheduledResidualMeasure (z : SamplingParameters×ℕ) : ℕ :=
  scheduledCountsMeasure z.1+originalEnumerationMeasure z.1.1+weight z

lemma work_scheduledResidualCache :
    WorkBound scheduledResidualCacheRealizer scheduledResidualMeasure := by
  have hi (z : SamplingParameters×ℕ) : weight z ≤ X.eval (scheduledResidualMeasure z) := by
    simp only [eval_X,scheduledResidualMeasure]
    omega
  have hc : WorkBound (composition (first (B := ℕ)) scheduledCountsRealizer)
      scheduledResidualMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_scheduledCounts X
    intro z
    simp only [eval_X,scheduledResidualMeasure]
    omega
  exact work_pair hc (work_of_polynomial (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) X hi) X hi

def cachedResidualInput (z : ScheduledResidualCache) : ResidualVectorCache :=
  ((originalCandidates z.2.1,z.1),((z.1.sum,z.2.2),originalCardinality z.2.1))

def cachedResidualInputRealizer : Realizer cachedResidualInput :=
  pair (pair (composition (f := fun z : ScheduledResidualCache => z.2.1) (g := originalCandidates)
    (composition second first) originalCandidatesRealizer) first)
    (pair (pair (composition first listSum) (composition second second))
      (composition (f := fun z : ScheduledResidualCache => z.2.1) (g := originalCardinality)
        (composition second first) originalCardinalityRealizer))

def cachedResidualMeasure (z : ScheduledResidualCache) : ℕ :=
  originalEnumerationMeasure z.2.1+weight z

lemma work_cachedResidualInput : WorkBound cachedResidualInputRealizer cachedResidualMeasure := by
  have hi (z : ScheduledResidualCache) : weight z ≤ X.eval (cachedResidualMeasure z) := by
    simp only [eval_X,cachedResidualMeasure]
    omega
  have he : WorkBound (composition (composition (second (A := List ℕ)) first)
      originalCandidatesRealizer) cachedResidualMeasure := by
    apply work_composition (work_of_polynomial (polynomial_composition polynomial_second polynomial_first)
      X hi) work_originalCandidates X
    intro z
    simp only [eval_X,cachedResidualMeasure,Function.comp_apply]
    omega
  have hn : WorkBound (composition (composition (second (A := List ℕ)) first)
      originalCardinalityRealizer) cachedResidualMeasure := by
    apply work_composition (work_of_polynomial (polynomial_composition polynomial_second polynomial_first)
      X hi) work_originalCardinality X
    intro z
    simp only [eval_X,cachedResidualMeasure,Function.comp_apply]
    omega
  exact work_pair (work_pair he (work_of_polynomial polynomial_first X hi) X hi)
    (work_pair (work_of_polynomial (polynomial_pair
      (polynomial_composition polynomial_first polynomial_listSum)
      (polynomial_composition polynomial_second polynomial_second)) X hi) hn X hi) X hi

def cachedResidualCounts (z : ScheduledResidualCache) : List ℕ :=
  residualVector (cachedResidualInput z)

def cachedResidualCountsRealizer : Realizer cachedResidualCounts :=
  composition (f := cachedResidualInput) (g := residualVector)
    cachedResidualInputRealizer residualVectorRealizer

lemma work_cachedResidualCounts : WorkBound cachedResidualCountsRealizer cachedResidualMeasure :=
  work_then_polynomial work_cachedResidualInput polynomial_residualVector

attribute [local irreducible] scheduledResidualCache cachedResidualCounts

/-- This computes the complete correction vector; it asks for no probability oracle. -/
def scheduledResidualCounts (z : SamplingParameters×ℕ) : List ℕ :=
  cachedResidualCounts (scheduledResidualCache z)

def scheduledResidualCountsRealizer : Realizer scheduledResidualCounts :=
  composition (f := scheduledResidualCache) (g := cachedResidualCounts)
    scheduledResidualCacheRealizer cachedResidualCountsRealizer

lemma work_scheduledResidualCounts :
    WorkBound scheduledResidualCountsRealizer scheduledResidualMeasure := by
  unfold scheduledResidualCountsRealizer scheduledResidualCounts
  obtain ⟨p,hp⟩ := work_scheduledResidualCache
  apply work_composition ⟨p,hp⟩ work_cachedResidualCounts (X+p)
  intro z
  have hw := hp z
  simp only [scheduledResidualCache] at hw
  simp only [eval_add,eval_X,cachedResidualMeasure,scheduledResidualCache]
  have hm : originalEnumerationMeasure z.1.1 ≤ scheduledResidualMeasure z := by
    unfold scheduledResidualMeasure
    omega
  omega

end ContingencyTables.ProfilePrograms

end OAI
