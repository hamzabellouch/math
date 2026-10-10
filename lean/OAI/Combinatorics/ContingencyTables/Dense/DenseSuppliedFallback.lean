import OAI.Combinatorics.ContingencyTables.Dense.DenseDrawTabulation

namespace OAI

/-! # Dense law tabulation retains the supplied feasible fallback -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

abbrev SuppliedTabulation := CanonicalParameters×MatrixCode

def replaceVectorFallback (z : VectorRetryPrograms.Input×ℕ) : VectorRetryPrograms.Input :=
  (z.1.1,(z.1.2.1,z.2))

def replaceVectorFallbackRealizer : Realizer replaceVectorFallback :=
  pair (composition first first) (pair (composition (composition first second) first) second)

lemma polynomial_replaceVectorFallback : PolynomialTime replaceVectorFallbackRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition (polynomial_composition polynomial_first
      polynomial_second) polynomial_first) polynomial_second)

def suppliedVectorInput (z : SuppliedTabulation) : VectorRetryPrograms.Input :=
  replaceVectorFallback (rawVectorInput z.1,tableIndex (z.1.1,z.2))

def suppliedVectorInputRealizer : Realizer suppliedVectorInput := by
  let base := composition (first (A := CanonicalParameters) (B := MatrixCode))
    rawVectorInputRealizer
  let margins : Realizer (fun z : SuppliedTabulation => z.1.1) := composition first first
  let query := pair margins (second (A := CanonicalParameters) (B := MatrixCode))
  let index := composition query tableIndexRealizer
  let result := composition (pair base index) replaceVectorFallbackRealizer
  exact result

def suppliedTabulationMeasure (z : SuppliedTabulation) : ℕ := rawTabulationMeasure z.1+weight z

lemma work_suppliedVectorInput : WorkBound suppliedVectorInputRealizer suppliedTabulationMeasure := by
  have hb : WorkBound (composition first rawVectorInputRealizer) suppliedTabulationMeasure := by
    apply work_composition (work_of_polynomial polynomial_first Polynomial.X
      (fun z => by simp only [suppliedTabulationMeasure,Polynomial.eval_X]; omega))
      work_rawVectorInput Polynomial.X
    intro z
    simp only [Polynomial.eval_X,suppliedTabulationMeasure]
    omega
  have hi : WorkBound (composition (pair (composition first first) second) tableIndexRealizer)
      suppliedTabulationMeasure :=
    work_of_polynomial (polynomial_composition
      (polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_tableIndex) Polynomial.X
      (fun z => by simp only [suppliedTabulationMeasure,Polynomial.eval_X]; omega)
  unfold suppliedVectorInputRealizer
  apply work_then_polynomial _ polynomial_replaceVectorFallback
  exact work_pair hb hi Polynomial.X
    (fun z => by simp only [suppliedTabulationMeasure,Polynomial.eval_X]; omega)

def suppliedDrawCounts (z : SuppliedTabulation) : List ℕ :=
  VectorRetryPrograms.counts (suppliedVectorInput z)

def suppliedDrawCountsRealizer : Realizer suppliedDrawCounts :=
  composition suppliedVectorInputRealizer VectorRetryPrograms.countsRealizer

theorem work_suppliedDrawCounts : WorkBound suppliedDrawCountsRealizer suppliedTabulationMeasure := by
  obtain ⟨p,hp⟩ := work_suppliedVectorInput
  obtain ⟨q,hq⟩ := VectorRetryPrograms.polynomial_counts
  refine ⟨p+q.comp p,fun z => ?_⟩
  have h1 := hp z
  have h2 := hq (suppliedVectorInput z)
  have h3 := polynomial_eval_monotone q ((Nat.le_add_left _ _).trans h1)
  dsimp only at h3
  simp only [Polynomial.eval_add,Polynomial.eval_comp]
  change suppliedVectorInputRealizer.cost z+
    VectorRetryPrograms.countsRealizer.cost (suppliedVectorInput z)+
    weight (VectorRetryPrograms.counts (suppliedVectorInput z))≤_
  omega

/-- The fallback is transported by the caller's normalization, rather
than being recomputed in the normalized margin order. -/
theorem suppliedDrawCounts_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (fallback : Table R P) :
    suppliedDrawCounts (((marginCode R,marginCode P),(d,h)),tableOutput fallback)=
      List.ofFn (((IndexedTableLaw.law R P (le_refl (∑ i,R i))
        ((denseTrialCounts R P d hd hR hP finProdFinEquiv h
          (canonicalOrigin (m*n) d (by omega))).push
            (trialSuccess R P d finProdFinEquiv htotal))).retry
        (IndexedTableLaw.index R P (le_refl (∑ i,R i)) fallback) (d^4*(h+1))).count) := by
  have hc : ∀ j : Fin (m*n),FairBits.offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d≤
        (unaryMarkers (denseTrialBits R P d finProdFinEquiv h)).length := by
    intro j
    rw [unaryMarkers_length]
    have hs : FairBits.offsetBitLength (integerWidth R P d (finProdFinEquiv.symm j)) h d≤
        ∑ k : Fin (m*n),FairBits.offsetBitLength
          (integerWidth R P d (finProdFinEquiv.symm k)) h d :=
      Finset.single_le_sum
        (f := fun k : Fin (m*n) => FairBits.offsetBitLength
          (integerWidth R P d (finProdFinEquiv.symm k)) h d)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact hs.trans (by unfold denseTrialBits; omega)
  unfold suppliedDrawCounts suppliedVectorInput replaceVectorFallback rawVectorInput rawCountContext
  rw [rawTrialBits_code (d := d) R P (show 0<d by omega),
    BinaryPowerPrograms.power_eq,tableIndex_actual]
  have he := denseRetryVector_actual R P hd hq hR hP htotal h
    (unaryMarkers (denseTrialBits R P d finProdFinEquiv h))
    (unaryMarkers (rawRepeat ((marginCode R,marginCode P),(d,h)))) hc fallback
  rw [unaryMarkers_length] at he
  simpa only [rawRepeat] using he

theorem suppliedDrawCounts_at {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (fallback X : Table R P) :
    (suppliedDrawCounts (((marginCode R,marginCode P),(d,h)),tableOutput fallback)).getD
      (tableIndex ((marginCode R,marginCode P),tableOutput X)) 0=
    (denseDrawCounts R P d hd hR hP finProdFinEquiv htotal h
      (canonicalOrigin (m*n) d (by omega)) fallback).count X := by
  rw [suppliedDrawCounts_actual R P hd hq hR hP htotal,tableIndex_actual]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,Fin.isLt,dite_true,
    Option.getD_some,Fin.eta]
  exact IndexedTableLaw.retry_count_index R P htotal (le_refl (∑ i,R i)) _
    fallback X (d^4*(h+1))

end ContingencyTables.DensePrograms

end OAI
