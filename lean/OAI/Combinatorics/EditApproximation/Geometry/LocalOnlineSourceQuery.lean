import OAI.Combinatorics.EditApproximation.Geometry.RefinementDataQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRawOnlineProgram
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Online ranges are computed from already gathered band data. The
following query reads only the scale/center pairs for the current entry,
then evaluates the existing local step with the returned integers. -/

namespace EditApproximation



theorem localOnlineSourceKeys_mem {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (b : ℕ)
    (hb : b ∈ dyadicQueryWindow N (initial q) a F) :
    (b, roundInterval (seedGridSpacing b P) q) ∈ localOnlineSourceKeys N P F a initial q :=
  List.mem_map.mpr ⟨b, hb, rfl⟩



theorem keyedOnlineSourceRange_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P exponent H : ℕ) (tau : ℚ)
    (child child' : Fin M → TargetInterval target.length → ℚ) (key : ℕ × TargetInterval target.length)
    (h : ∀ action ∈ wideActionList M parent key.2 key.1 P,
      ∀ i, child i (action i) = child' i (action i)) :
    keyedOnlineSourceRange source target parent P exponent H tau child key =
      keyedOnlineSourceRange source target parent P exponent H tau child' key := by
  unfold keyedOnlineSourceRange keyedOnlineBandG
  rw [representativeBandActions_congr_child source target parent key.2 key.1 P tau
    ((2 : ℚ) ^ (-(exponent : ℤ))) child child' h]

theorem keyedOnlineSourceRange_gathered {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child : Fin M → TargetInterval target.length → ℚ) (q : TargetInterval target.length)
    (b : ℕ) (hb : b ∈ dyadicQueryWindow N (parentInitial q) a F) :
    let keys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
    keyedOnlineSourceRange source target parent P exponent H tau
      (fun i r => finiteAnswerTable keys (keys.map fun input => child input.1 input.2) (i, r))
      (b, roundInterval (seedGridSpacing b P) q) =
    keyedOnlineSourceRange source target parent P exponent H tau child
      (b, roundInterval (seedGridSpacing b P) q) := by
  dsimp only
  apply keyedOnlineSourceRange_congr
  intro action ha i
  apply finiteAnswerTable_map
  exact wideWarmupInputs_pair parent P b _ _
    (queryEarlierRepresentatives_online N P F exponent a parentInitial q b hb) action ha i

section Query

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localOnlineSourceStepQuery_value (oracle : ι → ℚ)
    (integer : ℕ → TargetInterval target.length → ℕ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadInteger : ∀ key ∈ localOnlineSourceKeys N P F a parentInitial q,
      (readInteger key (keyedOnlineSourceRange source target parent P exponent H tau child key)).value oracle =
        (integer key.1 key.2 : ℚ))
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localOnlineSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw q readInteger readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  let keys := localOnlineSourceKeys N P F a parentInitial q
  let values := keys.map fun key =>
    (readInteger key (keyedOnlineSourceRange source target parent P exponent H tau child key)).value oracle
  let cached := fun b r => ⌊finiteAnswerTable keys values (b, r)⌋₊
  have hcached (b : ℕ) (hb : b ∈ dyadicQueryWindow N (parentInitial q) a F) :
      cached b (roundInterval (seedGridSpacing b P) q) =
        integer b (roundInterval (seedGridSpacing b P) q) := by
    have hmem := localOnlineSourceKeys_mem N P F a parentInitial q b hb
    dsimp only [cached, values]
    rw [finiteAnswerTable_map keys _ _ hmem, hreadInteger _ hmem]
    simp
  have honline := localOnlineCandidates_integer_congr source target parent N P F exponent H tau a eta kappa
    parentInitial child initial earlier (t - 1) cached integer q (fun b hb _ => hcached b hb)
  unfold localOnlineSourceStepQuery
  rw [FiniteQuery.collect_value]
  rw [localRefinementStepQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial child initial draw cached q readEarlier readCurrent oracle earlier current ht
    hreadEarlier hreadCurrent]
  rw [honline]

theorem localOnlineSourceStepQuery_cost (oracle : ι → ℚ) (weight : ι → ℕ) :
    (localOnlineSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw q readInteger readEarlier readCurrent).cost oracle weight =
    let keys := localOnlineSourceKeys N P F a parentInitial q
    let reader := fun key => readInteger key
      (keyedOnlineSourceRange source target parent P exponent H tau child key)
    (keys.map fun key => (reader key).cost oracle weight).sum +
      (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
        parentInitial child initial draw
        (fun b r => ⌊finiteAnswerTable keys (keys.map fun key => (reader key).value oracle) (b, r)⌋₊)
        q readEarlier readCurrent).cost oracle weight := by
  unfold localOnlineSourceStepQuery
  rw [FiniteQuery.cost_collect]

theorem localOnlineSourceKeys_length :
    (localOnlineSourceKeys N P F a parentInitial q).length =
      (dyadicQueryWindow N (parentInitial q) a F).length := by
  simp only [localOnlineSourceKeys, List.length_map]

end Query

end EditApproximation

end OAI
