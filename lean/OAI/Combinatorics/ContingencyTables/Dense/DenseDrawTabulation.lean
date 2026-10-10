import OAI.Combinatorics.ContingencyTables.Dense.DenseIndexedCounts
import OAI.Combinatorics.ContingencyTables.Machines.TableIndexProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseReservedWord

namespace OAI

/-! # Computing the full integer law of an initialized dense draw -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

def rawDrawParameters (z : CanonicalParameters) : DenseDrawParameters :=
  (((z.1,zeroGrid z.1),z.2.1),z.2.2)

def rawDrawParametersRealizer : Realizer rawDrawParameters := by
  let margins : Realizer (fun z : CanonicalParameters => z.1) := first
  let grid := composition margins zeroGridRealizer
  let result := pair (pair (pair margins grid) (composition second first))
    (composition second second)
  exact result

lemma polynomial_rawDrawParameters : PolynomialTime rawDrawParametersRealizer := by
  unfold rawDrawParametersRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition polynomial_first polynomial_zeroGrid))
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_composition polynomial_second polynomial_second)

def rawTrialBits (z : CanonicalParameters) : ℕ := trialWidth (rawDrawParameters z)

def rawTrialBitsRealizer : Realizer rawTrialBits :=
  composition rawDrawParametersRealizer trialWidthRealizer

lemma polynomial_rawTrialBits : PolynomialTime rawTrialBitsRealizer :=
  polynomial_composition polynomial_rawDrawParameters polynomial_trialWidth

def rawRepeat (z : CanonicalParameters) : ℕ := z.2.1^4*(z.2.2+1)

def rawRepeatRealizer : Realizer rawRepeat := by
  let d : Realizer (fun z : CanonicalParameters => z.2.1) := composition second first
  let h : Realizer (fun z : CanonicalParameters => z.2.2) := composition second second
  let result := composition (pair (composition d fourthPower)
    (composition h successor)) multiply
  exact result

lemma polynomial_rawRepeat : PolynomialTime rawRepeatRealizer := by
  unfold rawRepeatRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_fourthPower)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
      polynomial_successor)) polynomial_multiply

def rawCountContext (z : CanonicalParameters) : TrialCountContext :=
  ((tabulateDenseWalk z,unaryMarkers (rawTrialBits z)),z)

def rawCountContextRealizer : Realizer rawCountContext := by
  let cap := composition rawTrialBitsRealizer unaryMarkersRealizer
  let result := pair (pair tabulateDenseWalkRealizer cap) identity
  exact result

def rawFallbackIndex (z : CanonicalParameters) : ℕ :=
  tableIndex (z.1,GreedyFeasibleTable.listMatrix z.1.1 z.1.2)

def rawFallbackIndexRealizer : Realizer rawFallbackIndex :=
  composition (pair first (composition first GreedyFeasibleTable.tableRealizer)) tableIndexRealizer

lemma polynomial_rawFallbackIndex : PolynomialTime rawFallbackIndexRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_first GreedyFeasibleTable.polynomial_table)) polynomial_tableIndex

def rawVectorInput (z : CanonicalParameters) : VectorRetryPrograms.Input :=
  ((unaryMarkers (rawRepeat z),BinaryPowerPrograms.power (2,rawTrialBits z)),
    (candidateCounts (rawCountContext z),rawFallbackIndex z))

def rawVectorInputRealizer : Realizer rawVectorInput := by
  let markers := composition rawRepeatRealizer unaryMarkersRealizer
  let denominator := composition (pair (constant 2) rawTrialBitsRealizer)
    BinaryPowerPrograms.powerRealizer
  let counts := composition rawCountContextRealizer candidateCountsRealizer
  let result := pair (pair markers denominator) (pair counts rawFallbackIndexRealizer)
  exact result

def rawDrawCounts (z : CanonicalParameters) : List ℕ :=
  VectorRetryPrograms.counts (rawVectorInput z)

def rawDrawCountsRealizer : Realizer rawDrawCounts :=
  composition rawVectorInputRealizer VectorRetryPrograms.countsRealizer

def rawTabulationMeasure (z : CanonicalParameters) : ℕ :=
  tabulationMeasure z+gridStateCount (completionEnumerationData z.1)+rawTrialBits z+rawRepeat z

private lemma weight_le_rawMeasure (z : CanonicalParameters) : weight z≤rawTabulationMeasure z := by
  unfold rawTabulationMeasure tabulationMeasure
  omega

private lemma polynomial_work {A : Type} [Codec A] {f : CanonicalParameters → A}
    {F : Realizer f} (hF : PolynomialTime F) : WorkBound F rawTabulationMeasure :=
  work_of_polynomial hF Polynomial.X (fun z => by simpa using weight_le_rawMeasure z)

private lemma paired_work {A B : Type} [Codec A] [Codec B]
    {f : CanonicalParameters → A} {g : CanonicalParameters → B}
    {F : Realizer f} {G : Realizer g}
    (hF : WorkBound F rawTabulationMeasure) (hG : WorkBound G rawTabulationMeasure) :
    WorkBound (pair F G) rawTabulationMeasure :=
  work_pair hF hG Polynomial.X (fun z => by simpa using weight_le_rawMeasure z)

lemma work_rawCountContext : WorkBound rawCountContextRealizer rawTabulationMeasure := by
  have hw : WorkBound tabulateDenseWalkRealizer rawTabulationMeasure := by
    obtain ⟨p,hp⟩ := work_tabulateDenseWalk
    refine ⟨p,fun z => (hp z).trans ?_⟩
    apply polynomial_eval_monotone
    unfold rawTabulationMeasure
    omega
  have hc : WorkBound (composition rawTrialBitsRealizer unaryMarkersRealizer)
      rawTabulationMeasure := by
    apply work_composition (polynomial_work polynomial_rawTrialBits) work_unaryMarkers Polynomial.X
    intro z
    simp only [id_eq,Polynomial.eval_X,rawTabulationMeasure]
    omega
  unfold rawCountContextRealizer
  exact paired_work (paired_work hw hc) (polynomial_work polynomial_identity)

lemma work_rawCandidateCounts : WorkBound
    (composition rawCountContextRealizer candidateCountsRealizer) rawTabulationMeasure := by
  obtain ⟨p,hp⟩ := work_rawCountContext
  apply work_composition ⟨p,hp⟩ work_candidateCounts (Polynomial.X+p)
  intro z
  have hw := hp z
  simp only [candidateCountMeasure,rawCountContext,Polynomial.eval_add,Polynomial.eval_X]
  change _≤p.eval (rawTabulationMeasure z) at hw
  dsimp only [rawCountContext] at hw
  unfold rawTabulationMeasure at *
  omega

lemma work_rawVectorInput : WorkBound rawVectorInputRealizer rawTabulationMeasure := by
  have hj : WorkBound (composition rawRepeatRealizer unaryMarkersRealizer)
      rawTabulationMeasure := by
    apply work_composition (polynomial_work polynomial_rawRepeat) work_unaryMarkers Polynomial.X
    intro z
    simp only [id_eq,Polynomial.eval_X,rawTabulationMeasure]
    omega
  have hq : WorkBound (composition (pair (constant 2) rawTrialBitsRealizer)
      BinaryPowerPrograms.powerRealizer) rawTabulationMeasure := by
    apply work_composition (polynomial_work (polynomial_pair (polynomial_constant 2)
      polynomial_rawTrialBits)) BinaryPowerPrograms.work_power (Polynomial.X+9)
    intro z
    have htwo : weight (2:ℕ)≤9 := by decide
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,rawTabulationMeasure]
    omega
  unfold rawVectorInputRealizer
  exact paired_work (paired_work hj hq)
    (paired_work work_rawCandidateCounts (polynomial_work polynomial_rawFallbackIndex))

section
attribute [local irreducible] rawVectorInputRealizer VectorRetryPrograms.countsRealizer

/-- Full draw-law tabulation is polynomial in the finite box and grid
sizes and in the numerical precision schedules. -/
theorem work_rawDrawCounts : WorkBound rawDrawCountsRealizer rawTabulationMeasure := by
  obtain ⟨p,hp⟩ := work_rawVectorInput
  obtain ⟨q,hq⟩ := VectorRetryPrograms.polynomial_counts
  refine ⟨p+q.comp p,fun z => ?_⟩
  have h1 := hp z
  have h2 := hq (rawVectorInput z)
  have h3 := polynomial_eval_monotone q
    ((Nat.le_add_left _ _).trans h1)
  dsimp only at h3
  simp only [Polynomial.eval_add,Polynomial.eval_comp]
  change rawVectorInputRealizer.cost z+
    VectorRetryPrograms.countsRealizer.cost (rawVectorInput z)+
    weight (VectorRetryPrograms.counts (rawVectorInput z))≤_
  omega

end

lemma rawTrialBits_code {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 0<d) (h : ℕ) :
    rawTrialBits ((marginCode R,marginCode P),(d,h))=
      denseTrialBits R P d finProdFinEquiv h := by
  unfold rawTrialBits rawDrawParameters
  rw [zeroGrid_code R P hd]
  exact trialWidth_code R P h _

theorem rawDrawCounts_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ) :
    rawDrawCounts ((marginCode R,marginCode P),(d,h))=
      List.ofFn (((IndexedTableLaw.law R P (le_refl (∑ i,R i))
        ((denseTrialCounts R P d hd hR hP finProdFinEquiv h
          (canonicalOrigin (m*n) d (by omega))).push
            (trialSuccess R P d finProdFinEquiv htotal))).retry
        (IndexedTableLaw.index R P (le_refl (∑ i,R i)) (canonicalFallback R P htotal))
          (d^4*(h+1))).count) := by
  have hd0 : 0<d := by omega
  have hbits := rawTrialBits_code R P hd0 h
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
  unfold rawDrawCounts rawVectorInput rawCountContext rawFallbackIndex
  rw [hbits,BinaryPowerPrograms.power_eq,
    ←canonicalFallback_output R P htotal,
    tableIndex_actual]
  have he := denseRetryVector_actual R P hd hq hR hP htotal h
    (unaryMarkers (denseTrialBits R P d finProdFinEquiv h))
    (unaryMarkers (rawRepeat ((marginCode R,marginCode P),(d,h))))
    hc (canonicalFallback R P htotal)
  rw [unaryMarkers_length] at he
  simpa only [rawRepeat] using he

/-- Looking up a feasible table returns its exact numerator in the
implemented finite Boolean dense draw. -/
theorem rawDrawCounts_at {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (X : Table R P) :
    (rawDrawCounts ((marginCode R,marginCode P),(d,h))).getD
      (tableIndex ((marginCode R,marginCode P),tableOutput X)) 0=
    (denseDrawCounts R P d hd hR hP finProdFinEquiv htotal h
      (canonicalOrigin (m*n) d (by omega)) (canonicalFallback R P htotal)).count X := by
  rw [rawDrawCounts_actual R P hd hq hR hP htotal,tableIndex_actual]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,Fin.isLt,dite_true,
    Option.getD_some,Fin.eta]
  exact IndexedTableLaw.retry_count_index R P htotal (le_refl (∑ i,R i)) _
    (canonicalFallback R P htotal) X (d^4*(h+1))

end ContingencyTables.DensePrograms

end OAI
