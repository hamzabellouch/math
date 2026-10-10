import OAI.Combinatorics.ContingencyTables.Counting.CompanionCellCatalogProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionCanonicalEncoding

namespace OAI

/-! # Initialization from the computed small-cell catalog

The proof-level equivalence follows the actual catalog program. It is
used only to identify the output of the binary list initializer with a
paired transversal and to transfer its distributional error bound.
-/

namespace ContingencyTables.CompanionComputedInitial

open MatchingFPRAS.TreeTyped CompanionFactorialApplication
open InitialTransversals InitialFactorialBits CompanionInitialDraw
open FirstSuccess ResidualMixture TwoLiftStates CommonBasesFPRAS
open CompanionArithmeticProposal
open scoped BigOperators Classical

abbrev ProgramInput := (CompanionCellCatalog.Input×ℕ)×List Bool

def initialProgram (z : ProgramInput) : List ℕ :=
  CanonicalInitialEncoding.initialCode ((CompanionCellCatalog.capacities z.1.1,z.1.2),z.2)

def initialProgramRealizer : Realizer initialProgram :=
  composition (pair (pair
    (composition (composition first first) CompanionCellCatalog.capacitiesRealizer)
    (composition first second)) second) CanonicalInitialEncoding.initialCodeRealizer

theorem polynomial_initialProgram : PolynomialTime initialProgramRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      CompanionCellCatalog.polynomial_capacities)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second)
    CanonicalInitialEncoding.polynomial_initialCode

noncomputable section
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

def cellOrder : SmallCell A ≃ Fin (CompanionCellCatalog.catalog (CompanionCellCatalog.input A)).length :=
  (CompanionCellCatalog.cellEquiv A).symm

def capacities (i : Fin (CompanionCellCatalog.catalog (CompanionCellCatalog.input A)).length) : ℕ :=
  A.b ((cellOrder A).symm i).val.1 ((cellOrder A).symm i).val.2

def wordLength (B : ℕ) : ℕ := bitCount (capacities A) B

def initialDraw (B : ℕ) (bits : Fin (wordLength A B) → Bool) :
    PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) :=
  indexEquiv A (transversalDraw (fun s : SmallCell A => A.b s.val.1 s.val.2)
    (cellOrder A) B bits)

def copyOrder : Labels A ≃ Copy (capacities A) := Equiv.sigmaCongrLeft' (cellOrder A)

def pairOrder : (Labels A×Bool) ≃ (Copy (capacities A)×Bool) :=
  Equiv.prodCongr (copyOrder A) (Equiv.refl Bool)

def coordinateOrder : (Labels A×Bool) ≃ Fin (CanonicalInitialEncoding.pairOrder (capacities A)).length :=
  (pairOrder A).trans (CanonicalInitialEncoding.coordinateEquiv (capacities A))

lemma encodeSet_reindex (S : Set (Labels A×Bool)) :
    encodeSet (coordinateOrder A) S=
      encodeSet (CanonicalInitialEncoding.coordinateEquiv (capacities A))
        ((pairOrder A).symm ⁻¹' S) := rfl

lemma draw_preimage (B : ℕ) (bits : Fin (wordLength A B) → Bool) :
    (pairOrder A).symm ⁻¹' (initialDraw A B bits).val.val=
      encode (capacities A) (drawChoices (capacities A) B bits) := by
  ext p
  rcases p with ⟨⟨i,k⟩,side⟩
  have hc := Equiv.piCongrLeft'_symm_apply_apply
    (fun s : SmallCell A => Finset (Fin (A.b s.val.1 s.val.2)))
    (cellOrder A) (drawChoices (capacities A) B bits) i
  cases side
  · change k∈(choiceEquiv (fun s : SmallCell A => A.b s.val.1 s.val.2)
      (cellOrder A) (drawChoices (capacities A) B bits)) ((cellOrder A).symm i) ↔
        k∈drawChoices (capacities A) B bits i
    exact Iff.of_eq (congrArg (fun S => k∈S) hc)
  · change k∉(choiceEquiv (fun s : SmallCell A => A.b s.val.1 s.val.2)
      (cellOrder A) (drawChoices (capacities A) B bits)) ((cellOrder A).symm i) ↔
        k∉drawChoices (capacities A) B bits i
    exact Iff.of_eq (congrArg (fun S => k∉S) hc)

/-- The complete program computes the semantic initializer with the
coordinate order recovered from the program's own catalog. -/
theorem initialProgram_eq (B : ℕ) (hB : 0<B) (bits : Fin (wordLength A B) → Bool) :
    initialProgram ((CompanionCellCatalog.input A,B),List.ofFn bits)=
      encodeSet (coordinateOrder A) (initialDraw A B bits).val.val := by
  unfold initialProgram
  rw [CompanionCellCatalog.capacities_eq]
  rw [encodeSet_reindex,draw_preimage]
  exact CanonicalInitialEncoding.initialCode_ofFn (capacities A) B hB bits

lemma catalog_count_le : (CompanionCellCatalog.catalog (CompanionCellCatalog.input A)).length≤A.d := by
  have hc := Fintype.card_congr (CompanionCellCatalog.cellEquiv A)
  simpa only [Fintype.card_fin] using hc.trans_le (cellCount_bound A)

theorem wordLength_bound (B : ℕ) : wordLength A B≤A.d*(A.W+1)*B := by
  have hh := bitCount_bound (capacities A) B A.W (fun i =>
    (A.hsmall _ _ ((cellOrder A).symm i).property).le)
  exact hh.trans (Nat.mul_le_mul_right B
    (Nat.mul_le_mul_right (A.W+1) (catalog_count_le A)))

/-- The computed-order initializer has the same μ₀ reference law and
error guarantee as the abstract-order initializer. -/
theorem initialDraw_error (B : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (wordLength A B) → Bool)) (initialDraw A B))
      (idealLaw A)≤(A.d:ℚ)*(3*A.W+1)/(2*(2:ℚ)^B) := by
  unfold initialDraw wordLength capacities
  have he := mapLaw_equiv_output (indexEquiv A)
    (uniformLaw (α := Fin (bitCount
      (fun i => A.b ((cellOrder A).symm i).val.1 ((cellOrder A).symm i).val.2) B) → Bool))
    (transversalDraw (fun s : SmallCell A => A.b s.val.1 s.val.2) (cellOrder A) B)
  rw [he,idealLaw,variation_equiv]
  have ht := transversalDraw_error (fun s : SmallCell A => A.b s.val.1 s.val.2)
    (cellOrder A) B A.W (fun s => (A.hsmall _ _ s.property).le)
  apply ht.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast catalog_count_le A

theorem initialDraw_precision (h : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (wordLength A (precision A h)) → Bool))
      (initialDraw A (precision A h))) (idealLaw A)≤1/(2:ℚ)^h :=
  (initialDraw_error A (precision A h)).trans (precision_error A h)

end
end ContingencyTables.CompanionComputedInitial

end OAI
