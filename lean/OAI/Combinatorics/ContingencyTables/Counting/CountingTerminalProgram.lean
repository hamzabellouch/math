import OAI.Combinatorics.ContingencyTables.Counting.CountingBaseProgram

namespace OAI

/-! # The executed terminal grid width, cutoff and phase count -/

namespace ContingencyTables.CountingTerminalProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := CountingBaseProgram.Input

def base (z : Input) : ℕ :=
  CountingBaseProgram.coefficient z * CountingBaseProgram.dimension z.1 * CountingBaseProgram.dimension z.1
def baseRealizer : Realizer base :=
  composition (f := fun z : Input =>
      (CountingBaseProgram.coefficient z*CountingBaseProgram.dimension z.1,CountingBaseProgram.dimension z.1))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (pair CountingBaseProgram.coefficientRealizer
      (composition (f := fun z : Input => z.1) (g := CountingBaseProgram.dimension)
        first CountingBaseProgram.dimensionRealizer)) multiply)
      (composition (f := fun z : Input => z.1) (g := CountingBaseProgram.dimension)
        first CountingBaseProgram.dimensionRealizer)) multiply
lemma polynomial_base : PolynomialTime baseRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair CountingBaseProgram.polynomial_coefficient
      (polynomial_composition polynomial_first CountingBaseProgram.polynomial_dimension)) polynomial_multiply)
    (polynomial_composition polynomial_first CountingBaseProgram.polynomial_dimension)) polynomial_multiply

def binCount (z : Input) : ℕ := 16*base z
def binCountRealizer : Realizer binCount :=
  composition (f := fun z : Input => (16,base z)) (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (constant 16) baseRealizer) multiply
lemma polynomial_binCount : PolynomialTime binCountRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 16) polynomial_base) polynomial_multiply

def cutoff (z : Input) : ℕ := 100*CountingBaseProgram.dimension z.1*binCount z
def cutoffRealizer : Realizer cutoff :=
  composition (f := fun z : Input => (100*CountingBaseProgram.dimension z.1,binCount z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (f := fun z : Input => (100,CountingBaseProgram.dimension z.1))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 100) (composition (f := fun z : Input => z.1)
        (g := CountingBaseProgram.dimension) first CountingBaseProgram.dimensionRealizer)) multiply)
      binCountRealizer) multiply
lemma polynomial_cutoff : PolynomialTime cutoffRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 100)
      (polynomial_composition polynomial_first CountingBaseProgram.polynomial_dimension)) polynomial_multiply)
    polynomial_binCount) polynomial_multiply

def phases (z : Input) : ℕ := 10*base z*(cutoff z+1)
def phasesRealizer : Realizer phases :=
  composition (f := fun z : Input => (10*base z,cutoff z+1)) (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (f := fun z : Input => (10,base z)) (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 10) baseRealizer) multiply)
      (composition (f := cutoff) (g := fun n : ℕ => n+1) cutoffRealizer successor)) multiply
lemma polynomial_phases : PolynomialTime phasesRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 10) polynomial_base) polynomial_multiply)
    (polynomial_composition polynomial_cutoff polynomial_successor)) polynomial_multiply

lemma binCount_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    binCount (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.binCount r c b epsilon := by
  unfold binCount base
  rw [CountingBaseProgram.coefficient_data r c b epsilon he,
    CountingBaseProgram.dimension_data]
  unfold ComputedCountingParameters.binCount
  ring

lemma cutoff_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    cutoff (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.cutoff r c b epsilon := by
  unfold cutoff
  rw [CountingBaseProgram.dimension_data,binCount_data r c b epsilon he]
  rfl

lemma phases_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    phases (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.phases r c b epsilon := by
  unfold phases base
  rw [CountingBaseProgram.coefficient_data r c b epsilon he,
    CountingBaseProgram.dimension_data,cutoff_data r c b epsilon he]
  unfold ComputedCountingParameters.phases
  ring

end ContingencyTables.CountingTerminalProgram

end OAI
