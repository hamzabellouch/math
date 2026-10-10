import OAI.Combinatorics.EditApproximation.Geometry.RefinementBandSupport

namespace OAI

/-! Adaptive gathering of all fixed data used by one local refinement
entry: parent initial values, child warmup masses and child initial values.
Only the raw local support and the resulting wide coordinate lists are
requested. The later earlier/current gathers remain those of the literal
local refinement query. -/

namespace EditApproximation

section BandData

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

def localRefinementBandDataQuery : FiniteQuery ι :=
  let keys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
  FiniteQuery.collect readMass keys fun massValues =>
    FiniteQuery.collect readInitial keys fun initialValues =>
      localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
        parentInitial (fun i r => finiteAnswerTable keys massValues (i, r))
        (fun i r => finiteAnswerTable keys initialValues (i, r)) draw integer q readEarlier readCurrent

theorem localRefinementBandDataQuery_value (oracle : ι → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadMass : ∀ input, (readMass input).value oracle = child input.1 input.2)
    (hreadInitial : ∀ input, (readInitial input).value oracle = initial input.1 input.2)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRefinementBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial draw integer q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  let keys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
  let mass := fun i r => finiteAnswerTable keys (keys.map fun input => child input.1 input.2) (i, r)
  let initial' := fun i r => finiteAnswerTable keys (keys.map fun input => initial input.1 input.2) (i, r)
  have hmass : ∀ input ∈ keys, mass input.1 input.2 = child input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map keys _ input hi
  have hinitial : ∀ input ∈ keys, initial' input.1 input.2 = initial input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map keys _ input hi
  have honline := localOnlineCandidates_congr_bandTables source target parent N P F exponent H
    tau a eta kappa (t - 1) parentInitial mass child initial' initial earlier integer q hmass hinitial
  have hgroups := localCellGroupActions_congr_bandTables source target parent N P F exponent Q
    tau a parentInitial mass child initial' initial current draw q hmass hinitial
  unfold localRefinementBandDataQuery
  rw [FiniteQuery.collect_value]
  simp only [hreadMass]
  rw [FiniteQuery.collect_value]
  simp only [hreadInitial]
  rw [localRefinementStepQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial mass initial' draw integer q readEarlier readCurrent oracle earlier current ht
    hreadEarlier hreadCurrent]
  rw [honline]
  unfold rationalLocalWideStep
  rw [hgroups]

end BandData

section AllData

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (readParentInitial : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

def localRefinementDataQuery : FiniteQuery ι :=
  FiniteQuery.bind (readParentInitial q) fun value =>
    let keys := refinementInitialSupport N P F exponent a value q
    FiniteQuery.collect readParentInitial keys fun initialValues =>
      localRefinementBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
        (finiteAnswerTable keys initialValues) readMass readInitial draw integer q readEarlier readCurrent

theorem localRefinementDataQuery_value (oracle : ι → ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadParentInitial : ∀ r, (readParentInitial r).value oracle = parentInitial r)
    (hreadMass : ∀ input, (readMass input).value oracle = child input.1 input.2)
    (hreadInitial : ∀ input, (readInitial input).value oracle = initial input.1 input.2)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRefinementDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParentInitial readMass readInitial draw integer q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  let keys := refinementInitialSupport N P F exponent a (parentInitial q) q
  let cached := finiteAnswerTable keys (keys.map parentInitial)
  have heq : ∀ r ∈ refinementInitialSupport N P F exponent a (parentInitial q) q,
      parentInitial r = cached r := by
    intro r hr
    exact (finiteAnswerTable_map keys parentInitial r hr).symm
  have honline := localOnlineCandidates_congr_initial source target parent N P F exponent H
    tau a eta kappa (t - 1) parentInitial cached child initial earlier integer q heq
  have hstep := rationalLocalWideStep_congr_initial source target parent N P F exponent Q tau a
    parentInitial cached child initial current draw q heq delta (fun i r => earlier i (t - 1) r)
    (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial earlier (t - 1) integer q)
  unfold localRefinementDataQuery
  rw [FiniteQuery.bind_value, hreadParentInitial q, FiniteQuery.collect_value]
  simp only [hreadParentInitial]
  rw [localRefinementBandDataQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    cached readMass readInitial draw integer q readEarlier readCurrent oracle child initial earlier current ht
    hreadMass hreadInitial hreadEarlier hreadCurrent]
  rw [← honline]
  exact hstep.symm

end AllData

end EditApproximation

end OAI
