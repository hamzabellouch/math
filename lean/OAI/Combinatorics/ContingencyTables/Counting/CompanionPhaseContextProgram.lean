import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleConfigSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CountingPhaseParametersProgram

namespace OAI

/-! # Computing a phase configuration from immutable prepared data

The reserve is used only through its length. All precision-marker bits
are false, so the physical configuration is independent of the random
contents of the word that provides its bounded allocation.
-/

namespace ContingencyTables.CompanionPhaseContextProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Prepared := RootedOracleWalkProgram.State × CountingPhaseParametersProgram.Input
abbrev Input := (Prepared × ℕ) × List Bool

def noise (z : Input) : TreeFraction.Fraction := CountingPhaseParametersProgram.noise z.1.1.2
def noiseRealizer : Realizer noise :=
  composition (f := fun z : Input => z.1.1.2) (g := CountingPhaseParametersProgram.noise)
    (composition (composition first first) second) CountingPhaseParametersProgram.noiseRealizer
lemma polynomial_noise : PolynomialTime noiseRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_second) CountingPhaseParametersProgram.polynomial_noise

def precision (z : Input) : ℕ := CountingPhaseParametersProgram.precision z.1.1.2
def precisionRealizer : Realizer precision :=
  composition (f := fun z : Input => z.1.1.2) (g := CountingPhaseParametersProgram.precision)
    (composition (composition first first) second) CountingPhaseParametersProgram.precisionRealizer
lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_second) CountingPhaseParametersProgram.polynomial_precision

def scalar (e : ScalarScheduleProgram.Expr) (z : Input) : ℕ :=
  CountingPhaseParametersProgram.scalar e z.1.1.2
def scalarRealizer (e : ScalarScheduleProgram.Expr) : Realizer (scalar e) :=
  composition (f := fun z : Input => z.1.1.2) (g := CountingPhaseParametersProgram.scalar e)
    (composition (composition first first) second) (CountingPhaseParametersProgram.scalarRealizer e)
lemma polynomial_scalar (e : ScalarScheduleProgram.Expr) : PolynomialTime (scalarRealizer e) :=
  polynomial_composition (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_second) (CountingPhaseParametersProgram.polynomial_scalar e)

def falseReserve (z : Input) : List Bool := z.2.map (fun _ => false)
def falseReserveRealizer : Realizer falseReserve := composition second (map (constant false))
lemma polynomial_falseReserve : PolynomialTime falseReserveRealizer :=
  polynomial_composition polynomial_second (polynomial_map (polynomial_constant false))

def configInput (z : Input) : RootedOracleConfigProgram.Input :=
  (((z.1.1.1,noise z),z.1.2),falseReserve z)
def configInputRealizer : Realizer configInput :=
  pair (pair (pair (composition (composition first first) first) noiseRealizer)
    (composition first second)) falseReserveRealizer
lemma polynomial_configInput : PolynomialTime configInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_noise) (polynomial_composition polynomial_first polynomial_second)) polynomial_falseReserve

def config (z : Input) : RootedLabelWeightProgram.Config :=
  RootedOracleConfigProgram.output (configInput z)
def configRealizer : Realizer config :=
  composition (f := configInput) (g := RootedOracleConfigProgram.output)
    configInputRealizer RootedOracleConfigProgram.outputRealizer
theorem polynomial_config : PolynomialTime configRealizer :=
  polynomial_composition polynomial_configInput RootedOracleConfigProgram.polynomial_output

lemma falseReserve_length (z : Input) : (falseReserve z).length=z.2.length := List.length_map _

lemma falseReserve_eq (z : Input) : falseReserve z=List.replicate z.2.length false := by
  unfold falseReserve
  induction z.2 with
  | nil => rfl
  | cons b bs ih => simpa only [List.map_cons,List.length_cons,List.replicate_succ] using congrArg (List.cons false) ih

noncomputable section
open CompanionFactorialApplication CompanionOracleDensity GridBoundary
open scoped Classical
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool) : Input :=
  (((RootedOracleWalkProgram.data A C 0 K z v,parameters),j),reserve)

lemma config_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool) :
    config (data A C K j parameters z v reserve)=
      RootedOracleConfigProgram.output (RootedOracleConfigProgram.data A C K j
        (CountingPhaseParametersProgram.noise parameters) z v (List.replicate reserve.length false)) := by
  unfold config configInput noise data
  rw [falseReserve_eq]
  rfl

end
end ContingencyTables.CompanionPhaseContextProgram

end OAI
