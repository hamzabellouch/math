import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomSourceQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Gather data before selecting a random source coordinate. Online ranges
are calculated solely from previously requested band values; group draws and
online draws are ordinary scalar reads in the same adaptive query. -/

namespace EditApproximation

section BandData

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localRandomBandDataQuery_value (oracle : ι → ℚ)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadMass : ∀ input, (readMass input).value oracle = child input.1 input.2)
    (hreadInitial : ∀ input, (readInitial input).value oracle = initial input.1 input.2)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadGroup : ∀ key, (readGroup key).value oracle = groupScalarValue draw key)
    (hreadInteger : ∀ key,
      (readInteger key (keyedOnlineSourceRange source target parent P exponent H tau child key)).value oracle =
        (integer key.1 key.2 : ℚ))
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  classical
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
  unfold localRandomBandDataQuery
  rw [FiniteQuery.collect_value]
  simp only [hreadMass]
  rw [FiniteQuery.collect_value]
  simp only [hreadInitial]
  rw [localRandomSourceStepQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial mass initial' q readGroup readInteger readEarlier readCurrent oracle draw integer earlier current ht
    (fun key _ => hreadGroup key) ?_ hreadEarlier hreadCurrent]
  rotate_left
  · intro key hk
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
    rw [keyedOnlineSourceRange_gathered source target parent N P F exponent H tau a
      parentInitial child q b hb]
    exact hreadInteger _
  rw [honline]
  unfold rationalLocalWideStep
  rw [hgroups]

end BandData

section AllData

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (readParentInitial : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localRandomDataQuery_value (oracle : ι → ℚ)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadParentInitial : ∀ r, (readParentInitial r).value oracle = parentInitial r)
    (hreadMass : ∀ input, (readMass input).value oracle = child input.1 input.2)
    (hreadInitial : ∀ input, (readInitial input).value oracle = initial input.1 input.2)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadGroup : ∀ key, (readGroup key).value oracle = groupScalarValue draw key)
    (hreadInteger : ∀ key,
      (readInteger key (keyedOnlineSourceRange source target parent P exponent H tau child key)).value oracle =
        (integer key.1 key.2 : ℚ))
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRandomDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  classical
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
  unfold localRandomDataQuery
  rw [FiniteQuery.bind_value, hreadParentInitial q, FiniteQuery.collect_value]
  simp only [hreadParentInitial]
  rw [localRandomBandDataQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    cached readMass readInitial readGroup readInteger q readEarlier readCurrent oracle draw integer child initial earlier current ht
    hreadMass hreadInitial hreadEarlier hreadGroup hreadInteger hreadCurrent]
  rw [← honline]
  exact hstep.symm

end AllData

end EditApproximation

end OAI
