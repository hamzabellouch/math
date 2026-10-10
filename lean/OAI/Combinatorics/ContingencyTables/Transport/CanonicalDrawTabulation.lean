import OAI.Combinatorics.ContingencyTables.Dense.DenseSuppliedFallback

namespace OAI

/-! # Exact dense counts after computed maximal-margin normalization -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

def canonicalCountInput (z : CanonicalParameters) : SuppliedTabulation :=
  ((swapMargins (marginIndices z.1,z.1),z.2),
    swapMatrix (marginIndices z.1,GreedyFeasibleTable.listMatrix z.1.1 z.1.2))

def canonicalCountInputRealizer : Realizer canonicalCountInput := by
  let source : Realizer (fun z : CanonicalParameters => z.1) := first
  let indices := composition source marginIndicesRealizer
  let margins := composition (pair indices source) swapMarginsRealizer
  let fallback := composition source GreedyFeasibleTable.tableRealizer
  let precision : Realizer (fun z : CanonicalParameters => z.2) := second
  let result := pair (pair margins precision)
    (composition (pair indices fallback) swapMatrixRealizer)
  exact result

lemma polynomial_canonicalCountInput : PolynomialTime canonicalCountInputRealizer := by
  unfold canonicalCountInputRealizer
  exact polynomial_pair
    (polynomial_pair (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_marginIndices) polynomial_first)
      polynomial_swapMargins) polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_marginIndices)
      (polynomial_composition polynomial_first GreedyFeasibleTable.polynomial_table))
      polynomial_swapMatrix)

attribute [local irreducible] canonicalCountInputRealizer suppliedDrawCountsRealizer

def canonicalDrawCounts : CanonicalParameters → List ℕ :=
  suppliedDrawCounts ∘ canonicalCountInput

def canonicalDrawCountsRealizer : Realizer canonicalDrawCounts := by
  let result := composition (f := canonicalCountInput) (g := suppliedDrawCounts)
    canonicalCountInputRealizer suppliedDrawCountsRealizer
  exact result

def canonicalTabulationMeasure (z : CanonicalParameters) : ℕ :=
  suppliedTabulationMeasure (canonicalCountInput z)+weight z

section
attribute [local irreducible] canonicalCountInput suppliedDrawCounts

theorem work_canonicalDrawCounts :
    WorkBound (f := canonicalDrawCounts) canonicalDrawCountsRealizer canonicalTabulationMeasure := by
  obtain ⟨p,hp⟩ := polynomial_canonicalCountInput
  obtain ⟨q,hq⟩ := work_suppliedDrawCounts
  refine ⟨p+q,fun z => ?_⟩
  have h1 := (hp z).trans (polynomial_eval_monotone p
    (show weight z≤canonicalTabulationMeasure z from Nat.le_add_left _ _))
  have h2 := (hq (canonicalCountInput z)).trans (polynomial_eval_monotone q
    (show suppliedTabulationMeasure (canonicalCountInput z)≤canonicalTabulationMeasure z by
      exact Nat.le_add_right _ _))
  dsimp only at h1 h2
  simp only [Polynomial.eval_add]
  change canonicalCountInputRealizer.cost z+
    suppliedDrawCountsRealizer.cost (canonicalCountInput z)+
    weight (suppliedDrawCounts (canonicalCountInput z))≤_
  omega
end

/-- The lookup index uses exactly the same two swaps as the sampler. -/
def canonicalTableIndex (z : CanonicalParameters×MatrixCode) : ℕ :=
  tableIndex ((canonicalCountInput z.1).1.1,swapMatrix (marginIndices z.1.1,z.2))

def canonicalTableIndexRealizer : Realizer canonicalTableIndex := by
  let source : Realizer (fun z : CanonicalParameters×MatrixCode => z.1) := first
  let normalized := composition source canonicalCountInputRealizer
  let margins := composition (composition normalized first) first
  let originals : Realizer (fun z : CanonicalParameters×MatrixCode => z.1.1) :=
    composition first first
  let indices := composition originals marginIndicesRealizer
  let query := composition (pair indices second) swapMatrixRealizer
  exact composition (pair margins query) tableIndexRealizer

lemma polynomial_canonicalTableIndex : PolynomialTime canonicalTableIndexRealizer := by
  unfold canonicalTableIndexRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_canonicalCountInput)
      polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_marginIndices) polynomial_second) polynomial_swapMatrix)) polynomial_tableIndex

lemma canonicalCountInput_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j) (d h : ℕ) :
    canonicalCountInput ((marginCode R,marginCode P),(d,h))=
      (((marginCode (normalizedMargin R),marginCode (normalizedMargin P)),(d,h)),
        tableOutput (tableReindex (indexPermutation (marginPosition R))
          (indexPermutation (marginPosition P)) R P (canonicalFallback R P htotal))) := by
  unfold canonicalCountInput swapMargins marginIndices
  rw [←marginPosition_val,←marginPosition_val,marginCode_swap,marginCode_swap,
    ←canonicalFallback_output R P htotal,tableOutput_swap]
  rfl

lemma canonicalTableIndex_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j) (d h : ℕ) (X : Table R P) :
    canonicalTableIndex (((marginCode R,marginCode P),(d,h)),tableOutput X)=
      (IndexedTableLaw.index (normalizedMargin R) (normalizedMargin P)
        (le_refl (∑ i,normalizedMargin R i))
        (tableReindex (indexPermutation (marginPosition R))
          (indexPermutation (marginPosition P)) R P X)).val := by
  unfold canonicalTableIndex
  rw [canonicalCountInput_code R P htotal]
  simp only [marginIndices,←marginPosition_val]
  rw [tableOutput_swap]
  exact tableIndex_actual (normalizedMargin R) (normalizedMargin P) _

/-- The cached numerator is the count at the transported table, including
all fallback words of the actual normalized dense program. -/
theorem canonicalDrawCounts_at {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (X : Table R P) :
    (canonicalDrawCounts ((marginCode R,marginCode P),(d,h))).getD
      (canonicalTableIndex (((marginCode R,marginCode P),(d,h)),tableOutput X)) 0=
    (denseDrawCounts (normalizedMargin R) (normalizedMargin P) d hd
      (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
      finProdFinEquiv (by rw [normalizedMargin_total,normalizedMargin_total]; exact htotal) h
      (canonicalOrigin (m*n) d (by omega))
      (tableReindex (indexPermutation (marginPosition R))
        (indexPermutation (marginPosition P)) R P (canonicalFallback R P htotal))).count
      (tableReindex (indexPermutation (marginPosition R))
        (indexPermutation (marginPosition P)) R P X) := by
  dsimp only [canonicalDrawCounts,Function.comp_apply]
  rw [canonicalCountInput_code R P htotal,canonicalTableIndex_code R P htotal]
  have he := suppliedDrawCounts_at (normalizedMargin R) (normalizedMargin P) hd hq
    (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
    (by rw [normalizedMargin_total,normalizedMargin_total]; exact htotal) h
    (tableReindex (indexPermutation (marginPosition R))
      (indexPermutation (marginPosition P)) R P (canonicalFallback R P htotal))
    (tableReindex (indexPermutation (marginPosition R))
      (indexPermutation (marginPosition P)) R P X)
  have hi := tableIndex_actual (normalizedMargin R) (normalizedMargin P)
    (tableReindex (indexPermutation (marginPosition R))
      (indexPermutation (marginPosition P)) R P X)
  dsimp only [normalizedMargin] at he hi ⊢
  rw [hi] at he
  exact he

end ContingencyTables.DensePrograms

end OAI
