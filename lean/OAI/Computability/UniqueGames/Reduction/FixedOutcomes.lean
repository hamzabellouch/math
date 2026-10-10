import OAI.Computability.UniqueGames.Reduction.ExplicitLemmas
import OAI.Computability.UniqueGames.Reduction.OutputTranslationsLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.FixedOutcomes

open Integration.BinaryLinear ActualHomogeneous ActualSource
open ActualEnumeration UniqueGamesTheorem.Reduction.Explicit

variable {N : Type*}

abbrev Parameter (k s d : Nat) (N : Type*) :=
  (E k →ₗ[F2] ActualEnumeration.Ambient s d) × (N × (E k →ₗ[F2] F2))

def occurrenceTuples (m k : Nat) : List (Fin k → Fin m) :=
  functions (List.finRange m) k

/-- Ambient linear map, noise occurrence index, scalar linear functional,
in exactly the original nested enumeration order. -/
def fixedParams (k s d : Nat) (indices : List N) : List (Parameter k s d N) :=
  pairs (allLinearMaps k _ (ambientVectors s d))
    (pairs indices (allLinearMaps k F2 [0, 1]))

def assemble {m k s d : Nat} (U : Fin k → Fin m) (p : Parameter k s d N) :
    Query m k s d × (N × (E k →ₗ[F2] F2)) :=
  ((U, p.1), p.2)

/-- The reassociation changes only parentheses, not enumeration order. -/
def outcomeEquiv (m k s d : Nat) (N : Type*) :
    (Query m k s d × (N × (E k →ₗ[F2] F2))) ≃
      ((Fin k → Fin m) × Parameter k s d N) :=
  Equiv.prodAssoc _ _ _

private theorem pairs_associate {Left Middle Right : Type*}
    (xs : List Left) (ys : List Middle) (zs : List Right) :
    pairs (pairs xs ys) zs =
      xs.flatMap (fun x => (pairs ys zs).map (fun p => ((x, p.1), p.2))) := by
  simp only [pairs, List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem indexedOutcomes_factor (m k s d : Nat) (indices : List N) :
    ActualEnumeration.indexedOutcomes m k s d indices =
      (occurrenceTuples m k).flatMap (fun U => (fixedParams k s d indices).map (assemble U)) := by
  exact pairs_associate (functions (List.finRange m) k)
    (allLinearMaps k _ (ambientVectors s d))
    (pairs indices (allLinearMaps k F2 [0, 1]))

theorem indexedOutcomes_reassociate (m k s d : Nat) (indices : List N) :
    (ActualEnumeration.indexedOutcomes m k s d indices).map (outcomeEquiv m k s d N) =
      pairs (occurrenceTuples m k) (fixedParams k s d indices) := by
  rw [indexedOutcomes_factor]
  simp only [pairs, List.map_flatMap, List.map_map, Function.comp_def,
    assemble, outcomeEquiv, Equiv.prodAssoc_apply]

theorem occurrenceTuples_length (m k : Nat) : (occurrenceTuples m k).length = m^k := by
  simp only [occurrenceTuples, length_functions, List.length_finRange]

theorem fixedParams_length (k s d : Nat) (indices : List N) :
    (fixedParams k s d indices).length = 2^((2*k+1)*(s+d+1)) * indices.length := by
  simp only [fixedParams, length_pairs, length_allLinearMaps, length_ambientVectors,
    List.length_cons, List.length_nil, ← pow_mul]
  change 2^((s+d)*(2*k+1)) * (indices.length * 2^(2*k+1)) =
    2^((2*k+1)*(s+d+1)) * indices.length
  rw [show (2*k+1)*(s+d+1) = (s+d)*(2*k+1)+(2*k+1) by ring, pow_add]
  ring

theorem fixedParams_nonempty (k s d : Nat) {indices : List N} (hne : indices ≠ []) :
    fixedParams k s d indices ≠ [] := by
  apply List.length_pos_iff.mp
  rw [fixedParams_length]
  exact Nat.mul_pos (Nat.two_pow_pos _) (List.length_pos_iff.mpr hne)

/-- A coefficient-only representation of each fixed linear-map parameter. -/
abbrev CoefficientParameter (k s d : Nat) (N : Type*) :=
  Coefficients k (ActualEnumeration.Ambient s d) × (N × Coefficients k F2)

def coefficientValues {Value : Type*} (k : Nat) (values : List Value) :
    List (Coefficients k Value) :=
  pairs values (functions (pairs values values) k)

def fixedCoefficientParams (k s d : Nat) (indices : List N) :
    List (CoefficientParameter k s d N) :=
  pairs (coefficientValues k (ambientVectors s d))
    (pairs indices (coefficientValues k ([0, 1] : List F2)))

def fromCoefficientParameter {k s d : Nat} (p : CoefficientParameter k s d N) :
    Parameter k s d N :=
  (coefficientEquiv k _ p.1, (p.2.1, coefficientEquiv k F2 p.2.2))

/-- The concrete coefficient enumeration produces precisely the fixed parameter
list. No choice of maps or representatives is made by this constructor. -/
theorem fixedCoefficientParams_map (k s d : Nat) (indices : List N) :
    (fixedCoefficientParams k s d indices).map fromCoefficientParameter =
      fixedParams k s d indices := by
  simp only [fixedCoefficientParams, fixedParams, coefficientValues, allLinearMaps,
    pairs, List.map_flatMap, List.flatMap_assoc, List.flatMap_map, List.map_map, Function.comp_def,
    fromCoefficientParameter]

theorem fixedCoefficientParams_length (k s d : Nat) (indices : List N) :
    (fixedCoefficientParams k s d indices).length =
      2^((2*k+1)*(s+d+1)) * indices.length := by
  rw [← fixedParams_length k s d indices, ← fixedCoefficientParams_map, List.length_map]

def tableParams (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    List (Parameter k s d (Fin T.vectors.length)) :=
  fixedParams k s d (List.finRange T.vectors.length)

theorem tableParams_length (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    (tableParams k T).length = 2^((2*k+1)*(s+d+1)) * T.vectors.length := by
  simp only [tableParams, fixedParams_length, List.length_finRange]

theorem outputInstance_constraints (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (AddressGame.outputInstance S k g en).constraints =
      (occurrenceTuples S.occurrences k).flatMap (fun U =>
        (fixedParams k s d en.indices).map (fun p =>
          AddressGame.addressEdge S k g (assemble U p))) := by
  change (ActualEnumeration.indexedOutcomes S.occurrences k s d en.indices).map
    (AddressGame.addressEdge S k g) = _
  rw [indexedOutcomes_factor]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

theorem tableOutput_constraints (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    (AddressGame.tableOutput S k T).constraints =
      (occurrenceTuples S.occurrences k).flatMap (fun U =>
        (tableParams k T).map (fun p => AddressGame.addressEdge S k
          (Integration.TableReduction.tableSkeleton T) (assemble U p))) :=
  outputInstance_constraints S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

end UniqueGamesTheorem.Reduction.FixedOutcomes

end

end OAI
