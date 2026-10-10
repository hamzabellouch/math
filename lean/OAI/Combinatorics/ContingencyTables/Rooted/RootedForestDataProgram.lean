import OAI.Combinatorics.ContingencyTables.Rooted.RootedOffsetProgram

namespace OAI

/-! # Preparing a tree penalty from executed coefficients and offsets

All signed affine data are computed internally from the graph, capacities,
baseline and two stored views. Only ordinary cell indices and values occur
in the input; no affine coefficient or offset is supplied.
-/

namespace ContingencyTables.RootedForestDataProgram

open MatchingFPRAS.TreeTyped SignedPairProgram
open scoped Classical

abbrev TermInput := RootedCoefficientProgram.Input×ℕ
abbrev Input := ((ℕ×ℕ)×RootedOffsetProgram.Input)×List TermInput

def scale (z : ℕ×Signed) : Signed :=
  SignedPairProgram.normalize (times ((z.1,0),z.2))

def scaleRealizer : Realizer scale :=
  composition (f := fun z : ℕ×Signed => times ((z.1,0),z.2))
    (g := SignedPairProgram.normalize)
    (composition (f := fun z : ℕ×Signed => ((z.1,0),z.2)) (g := times)
      (pair (pair first (constant 0)) second) timesRealizer) normalizeRealizer

lemma polynomial_scale : PolynomialTime scaleRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_pair polynomial_first (polynomial_constant 0)) polynomial_second)
    polynomial_times) polynomial_normalize

lemma scale_value (n : ℕ) (z : Signed) :
    scale (n,z)=ForestAffineProgram.signedParts ((n:ℤ)*value z) := by
  rw [scale,normalize_eq,value_times]
  rfl

def term (z : TermInput) : ForestAffineProgram.Term :=
  (scale (z.1.2.2+1,RootedCoefficientProgram.coefficient z.1),z.2)

def termRealizer : Realizer term :=
  pair
    (composition (f := fun z : TermInput =>
      (z.1.2.2+1,RootedCoefficientProgram.coefficient z.1)) (g := scale) (pair
      (composition (composition (composition first second) second) successor)
      (composition (f := fun z : TermInput => z.1) (g := RootedCoefficientProgram.coefficient)
        first RootedCoefficientProgram.coefficientRealizer)) scaleRealizer)
    second

lemma polynomial_term : PolynomialTime termRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_second) polynomial_successor)
    (polynomial_composition polynomial_first RootedCoefficientProgram.polynomial_coefficient))
    polynomial_scale) polynomial_second

def numeratorOffset (z : Input) : Signed :=
  scale (z.1.1.1,RootedOffsetProgram.offset z.1.2)

def numeratorOffsetRealizer : Realizer numeratorOffset :=
  composition (f := fun z : Input => (z.1.1.1,RootedOffsetProgram.offset z.1.2)) (g := scale)
    (pair (composition (composition first first) first)
      (composition (f := fun z : Input => z.1.2) (g := RootedOffsetProgram.offset)
        (composition first second) RootedOffsetProgram.offsetRealizer)) scaleRealizer

lemma polynomial_numeratorOffset : PolynomialTime numeratorOffsetRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      RootedOffsetProgram.polynomial_offset)) polynomial_scale

def prepare (z : Input) : ForestAffineProgram.Input :=
  ((numeratorOffset z,z.2.map term),z.1.1.1*z.1.1.2)

def prepareRealizer : Realizer prepare :=
  pair (pair numeratorOffsetRealizer (composition second (map termRealizer)))
    (composition (composition first first) multiply)

theorem polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair polynomial_numeratorOffset
    (polynomial_composition polynomial_second (polynomial_map polynomial_term)))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_multiply)

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation ForestAssignmentSplit

lemma term_input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) (v : ℕ) :
    term (RootedCoefficientProgram.input A t a,v)=
      (ForestAffineProgram.signedParts
        (RootedIntegerEvaluation.coefficient A (rowColumn A.T) t a*((A.b a.1 a.2:ℤ)+1)),v) := by
  unfold term
  rw [scale_value,RootedCoefficientProgram.coefficient_input]
  simp only [RootedCoefficientProgram.input,Nat.cast_add,Nat.cast_one]
  congr 2
  ring

noncomputable def data {m n nc nf : ℕ} (A : Instance (Fin m) (Fin n))
    (B : ℕ) (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (cells : Fin nc ≃ Fin m×Fin n) (free : Fin nf ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) : Input :=
  (((B,A.b t.val.1 t.val.2),RootedOffsetProgram.data A t x q cells),
    List.ofFn (fun i => (RootedCoefficientProgram.input A t (free i).val,v (free i))))

/-- The generated binary input equals the exact affine tree input used
by the selected-root penalty evaluation. -/
theorem prepare_data {m n nc nf : ℕ} (A : Instance (Fin m) (Fin n))
    (B : ℕ) (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (cells : Fin nc ≃ Fin m×Fin n) (free : Fin nf ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) :
    prepare (data A B t x q cells free v)=
      RootedIntegerEvaluation.forestData A (rowColumn A.T) B t x q free v := by
  have ht : (List.ofFn (fun i : Fin nf =>
      (RootedCoefficientProgram.input A t (free i).val,v (free i)))).map term=
      List.ofFn (fun i : Fin nf => (ForestAffineProgram.signedParts
        (RootedIntegerEvaluation.coefficient A (rowColumn A.T) t (free i).val*
          ((A.b (free i).val.1 (free i).val.2:ℤ)+1)),v (free i))) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact term_input A t (free i).val (v (free i))
  unfold prepare numeratorOffset data RootedIntegerEvaluation.forestData ForestAffineProgram.data
  rw [RootedOffsetProgram.offset_data,scale_value,ht]
  simp only [RootedOffsetProgram.value_parts]

theorem evaluate_prepare {m n nc nf : ℕ} (A : Instance (Fin m) (Fin n))
    (B : ℕ) (hB : 0<B) (t : GraphCompletionCounts.TreeCell A.T)
    (x q : Fin m → Fin n → ℤ) (cells : Fin nc ≃ Fin m×Fin n)
    (free : Fin nf ≃ FreeCell A.small A.T) (v : FreeCell A.small A.T → ℕ) :
    MatchingFPRAS.TreeFraction.val
        (ForestAffineProgram.evaluate (prepare (data A B t x q cells free v)))=
      max 0 (max (-rationalScaledTree A (rowColumn A.T) B x q (fun f => (v f:ℚ)) t)
        (rationalScaledTree A (rowColumn A.T) B x q (fun f => (v f:ℚ)) t-1)) := by
  rw [prepare_data]
  exact evaluate_forest A (rowColumn A.T) B hB t x q free v

end ContingencyTables.RootedForestDataProgram

end OAI
