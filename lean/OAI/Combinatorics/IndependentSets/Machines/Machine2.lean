import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PoweringLabels
import OAI.Combinatorics.IndependentSets.Encoding.FormulaEncoding
import OAI.Combinatorics.IndependentSets.Expansion.PreprocessingPaddingOffsets
import OAI.Combinatorics.IndependentSets.Expansion.ExpanderTableWords

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity

def naturalWordsEncoding : Computability.Encoding (List Nat) Bool where
  encode := encodeWords
  decode := decodeWords
  decode_encode := decodeWords_encodeWords

def formulaEncoding : Computability.Encoding Target.Formula Bool where
  encode := formulaBits
  decode := decodeFormulaBits
  decode_encode := decodeFormulaBits_encoded

def gameEncoding (alphabet : Nat) : Computability.Encoding (Target.Instance alphabet) Bool where
  encode := gameBits
  decode := decodeGameBits alphabet
  decode_encode := decodeGameBits_encoded

def prefixBitMachine (bit : Bool) : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .push () (fun _ => bit) .halt

noncomputable def prefixBitPolyTime (bit : Bool) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id (bit :: ·) where
  tm := prefixBitMachine bit
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun bs := {
    steps := 1
    evals_in_steps := by
      change some (Turing.TM2.stepAux (.push () (fun _ => bit) .halt) ()
          (fun _ : Unit => bs.map id)) =
        some { l := none, var := (), stk := fun _ : Unit => (bit :: bs).map id }
      simp [Turing.TM2.stepAux]
      funext k
      cases k
      rfl
    steps_le_m := by simp
  }

def enlargePolynomialBound {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f)
    (bound : Polynomial Nat)
    (larger : ∀ n, certificate.time.eval n ≤ bound.eval n) :
    Turing.TM2ComputableInPolyTime ea eb f where
  toTM2ComputableAux := certificate.toTM2ComputableAux
  time := bound
  outputsFun a := {
    toEvalsTo := (certificate.outputsFun a).toEvalsTo
    steps_le_m := Nat.le_trans (certificate.outputsFun a).steps_le_m (larger _)
  }

def composeMachinePhases {σ : Type} (step : σ → Option σ)
    (start intermediate : σ) (finish : Option σ)
    (p q : Polynomial Nat) (inputLength : Nat)
    (first : StateTransition.EvalsToInTime step start (some intermediate) (p.eval inputLength))
    (second : StateTransition.EvalsToInTime step intermediate finish (q.eval inputLength)) :
    StateTransition.EvalsToInTime step start finish ((p + q).eval inputLength) := by
  have composed := StateTransition.EvalsToInTime.trans step (p.eval inputLength)
    (q.eval inputLength) start intermediate finish first second
  simpa only [Polynomial.eval_add, Nat.add_comm] using composed

open Target

structure PolynomialGapReduction
    (completenessError soundnessError : RationalError)
    extends SemanticGapReduction completenessError soundnessError where
  computation : Turing.TM2ComputableInPolyTime formulaEncoding.encode
    (gameEncoding alphabet).encode reduce

end IndependentSetsGames.Foundations.Complexity

namespace IndependentSetsGames.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open IndependentSetsGames.Foundations.Complexity
open scoped BigOperators

def inputLength (t : GraphTables.Table) : Nat := (GraphTables.tableBits t).length

theorem cloudSize_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    cloudSize t v ≤ inputLength t :=
  (cloudSize_le_darts t v).trans (GraphTables.darts_le_tableBits_length t)

theorem cloudTotal_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    cloudSize t v + padding t v ≤ ExpanderFamily.growth * inputLength t := by
  rw [cloudSize_add_padding]
  exact (PreprocessingLevels.cloudPaddedSize_bounds _).2.trans
    (Nat.mul_le_mul_left _ (cloudSize_le_input t v))

theorem level_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    PreprocessingLevels.boundedLevel (cloudSize t v) ≤ inputLength t :=
  (PreprocessingLevels.boundedLevel_le_input _).trans (cloudSize_le_input t v)

theorem regularVertices_le_input (t : GraphTables.Table) :
    vertexCount t (padding t) ≤ ExpanderFamily.growth * inputLength t :=
  (vertexCount_le t).trans
    (Nat.mul_le_mul_left _ (GraphTables.darts_le_tableBits_length t))

theorem offset_le_sum {n : Nat} (p : Fin n → Nat) (k : Nat) :
    PreprocessingPaddingOffsets.offset p k ≤ ∑ v, p v := by
  have hfull : (List.finRange n).take n = List.finRange n := by simp
  have hsplit : PreprocessingPaddingOffsets.offset p k +
      (((List.finRange n).drop k).map p).sum =
      PreprocessingPaddingOffsets.offset p n := by
    simp only [PreprocessingPaddingOffsets.offset, hfull]
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  rw [PreprocessingPaddingOffsets.offset_all] at hsplit
  omega

theorem prefix_le_input (t : GraphTables.Table) (k : Nat) :
    PreprocessingPaddingOffsets.offset (padding t) k ≤
      ExpanderFamily.growth * inputLength t := by
  have hsum : (∑ v, padding t v) ≤ vertexCount t (padding t) := by
    unfold vertexCount
    omega
  exact (offset_le_sum (padding t) k).trans (hsum.trans (regularVertices_le_input t))

noncomputable def tablePolynomial (a b : Nat) : Polynomial Nat :=
  Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 2 +
    (Polynomial.C b * Polynomial.X) *
      (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 8192)

theorem tableBits_le_of_counts (t : GraphTables.Table) (a b L : Nat)
    (hv : t.vertices ≤ a * L) (he : t.darts ≤ b * L) :
    (GraphTables.tableBits t).length ≤ (tablePolynomial a b).eval L := by
  have hsum := Nat.add_le_add hv he
  have hprod := Nat.mul_le_mul he (Nat.add_le_add_right hsum 8192)
  have h := (GraphTables.tableBits_length_le t).trans
    (Nat.add_le_add (Nat.add_le_add_right hsum 2) hprod)
  simpa only [tablePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

noncomputable def regularPolynomial : Polynomial Nat :=
  tablePolynomial ExpanderFamily.growth (ExpanderFamily.growth * (internalDegree + 1))

theorem regularBits_le (H : BaseTable) (t : GraphTables.Table) :
    (PortTables.tableBits (regularize H t)).length ≤
      regularPolynomial.eval (inputLength t) := by
  have hv : (PortTables.graphTable (regularize H t)).vertices ≤
      ExpanderFamily.growth * inputLength t := regularVertices_le_input t
  have he : (PortTables.graphTable (regularize H t)).darts ≤
      (ExpanderFamily.growth * (internalDegree + 1)) * inputLength t := by
    change vertexCount t (padding t) * (internalDegree + 1) ≤ _
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * (internalDegree + 1) :=
        Nat.mul_le_mul_right _ hv
      _ = _ := by ac_rfl
  exact tableBits_le_of_counts (PortTables.graphTable (regularize H t)) _ _ _ hv he

noncomputable def rotorPolynomial (q : Nat) : Polynomial Nat :=
  (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X) *
    (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X + 1)

theorem cloudRotorBits_le (t : GraphTables.Table) (v : Fin t.vertices) {q : Nat}
    (table : ExpanderTables.Table (cloudSize t v + padding t v) q) :
    (encodeWords (ExpanderTableWords.rotationWords table)).length ≤
      (rotorPolynomial q).eval (inputLength t) := by
  have hd : (cloudSize t v + padding t v) * q ≤
      (ExpanderFamily.growth * q) * inputLength t := by
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * q :=
        Nat.mul_le_mul_right _ (cloudTotal_le_input t v)
      _ = _ := by ac_rfl
  have h := (ExpanderTableWords.encode_rotationWords_length_le table).trans
    (Nat.mul_le_mul hd (Nat.add_le_add_right hd 1))
  simpa only [rotorPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end IndependentSetsGames.Foundations.PCP.PreprocessingMachineBounds

end OAI
