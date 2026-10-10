import OAI.Combinatorics.ContingencyTables.Counting.CountingCoefficientProgram
import OAI.Combinatorics.ContingencyTables.Counting.ComputedCountingParameters

namespace OAI

/-! # Executing the capacity-bit and dimension inputs to the counting schedule -/

namespace ContingencyTables.CountingBaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open NetworkVertexCode

abbrev Input := NetworkVertexCode.Input × TreeFraction.Fraction

def cellBits (x : ℕ) : ℕ := (x+1).size
def cellBitsRealizer : Realizer cellBits :=
  (composition (composition successor toBits) listLength).congr
    (fun x => Nat.size_eq_bits_len (x+1))
lemma polynomial_cellBits : PolynomialTime cellBitsRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_composition polynomial_successor polynomial_toBits) polynomial_listLength)

def capacityBits (z : NetworkVertexCode.Input) : ℕ :=
  (((TightenedInputProgram.compute z).2.flatten).map cellBits).sum
def capacityBitsRealizer : Realizer capacityBits :=
  composition (f := fun z : NetworkVertexCode.Input => (TightenedInputProgram.compute z).2.flatten)
    (g := fun xs : List ℕ => (xs.map cellBits).sum)
    (composition (composition TightenedInputProgram.computeRealizer second) flatten)
    (composition (map cellBitsRealizer) listSum)
lemma polynomial_capacityBits : PolynomialTime capacityBitsRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition TightenedInputProgram.polynomial_compute polynomial_second)
      polynomial_flatten)
    (polynomial_composition (polynomial_map polynomial_cellBits) polynomial_listSum)

def dimension (z : NetworkVertexCode.Input) : ℕ := 1+z.1.1.length*z.1.2.length
def dimensionRealizer : Realizer dimension :=
  composition (f := fun z : NetworkVertexCode.Input => (1,z.1.1.length*z.1.2.length))
    (g := fun p : ℕ×ℕ => p.1+p.2) (pair (constant 1)
    (composition (pair (composition (composition first first) listLength)
      (composition (composition first second) listLength)) multiply)) add
lemma polynomial_dimension : PolynomialTime dimensionRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 1)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_listLength)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_listLength))
      polynomial_multiply)) polynomial_add

def half (e : TreeFraction.Fraction) : TreeFraction.Fraction := (e.1,2*e.2)
def halfRealizer : Realizer half :=
  pair first (composition (f := fun e : TreeFraction.Fraction => (2,e.2))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair (constant 2) second) multiply)
lemma polynomial_half : PolynomialTime halfRealizer :=
  polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_second) polynomial_multiply)

lemma half_val (e : TreeFraction.Fraction) : TreeFraction.val (half e)=TreeFraction.val e/2 := by
  simp only [half,TreeFraction.val,Nat.cast_mul,Nat.cast_ofNat]
  ring

def frame (z : Input) : CountingCoefficientProgram.Input :=
  ((capacityBits z.1,dimension z.1),half z.2)
def frameRealizer : Realizer frame :=
  pair (pair
    (composition (f := fun z : Input => z.1) (g := capacityBits) first capacityBitsRealizer)
    (composition (f := fun z : Input => z.1) (g := dimension) first dimensionRealizer))
    (composition (f := fun z : Input => z.2) (g := half) second halfRealizer)
lemma polynomial_frame : PolynomialTime frameRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_capacityBits)
    (polynomial_composition polynomial_first polynomial_dimension))
    (polynomial_composition polynomial_second polynomial_half)

def coefficient (z : Input) : ℕ := CountingCoefficientProgram.coefficient (frame z)
def coefficientRealizer : Realizer coefficient :=
  composition (f := frame) (g := CountingCoefficientProgram.coefficient)
    frameRealizer CountingCoefficientProgram.coefficientRealizer
lemma polynomial_coefficient : PolynomialTime coefficientRealizer :=
  polynomial_composition polynomial_frame CountingCoefficientProgram.polynomial_coefficient

lemma capacityBits_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    capacityBits (data r c b)=ComputedCountingParameters.capacityBits r c b := by
  unfold capacityBits
  rw [TightenedInputProgram.compute_code]
  simp only [data,ResidualGraphProgram.natCode,List.map_flatten,List.map_ofFn,Function.comp_def,
    List.sum_flatten,List.sum_ofFn,cellBits,ComputedCountingParameters.capacityBits,
    Fintype.sum_prod_type]

lemma dimension_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    dimension (data r c b)=ComputedCountingParameters.dimensionAllowance (m:=m) (n:=n) := by
  simp only [dimension,data,List.length_ofFn,ComputedCountingParameters.dimensionAllowance]

lemma coefficient_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    coefficient (data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.coefficient r c b epsilon := by
  unfold coefficient frame
  rw [capacityBits_data,dimension_data]
  have hn : 0 < (half (TreeFraction.repr epsilon)).1 := by
    change 0 < epsilon.num.natAbs
    exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr he))
  have hd : 0 < (half (TreeFraction.repr epsilon)).2 := by
    change 0 < 2*epsilon.den
    exact Nat.mul_pos (by decide) epsilon.pos
  rw [CountingCoefficientProgram.coefficient_val _ _ _ hn hd,half_val,
    TreeFraction.val_repr he.le]
  rfl

end ContingencyTables.CountingBaseProgram

end OAI
