import OAI.Combinatorics.EditApproximation.Refinement.PhysicalScalarReads
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomValue
import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineMassBound
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalJointProgram
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Finite independent scalar sources for all passes and copies. The
incoming seed selects the range only after the earlier passes are evaluated. -/

namespace EditApproximation

section Family

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (hP : 0 < P)





variable (draw : PhysicalFamilyScalarDraw
  (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)

def physicalFamilyDraw (pass copy : ℕ) :
    PhysicalScalarDraw M J N target.length exponent F Q R (localOnlineMassBound M P H) :=
  fun key => draw (Fin.ofNat (passes + 1) pass, Fin.ofNat (copies + 1) copy, key)







noncomputable def physicalFamilySample (seed : PhysicalEntry M J target.length → ℕ) (pass copy : ℕ) :=
  physicalCommonSample source target seed N P F (factor pass) T exponent H Q R
    (localOnlineMassBound M P H) tau
    (physicalLocalOnlineMass_le source target seed N P F (factor pass) T exponent H tau hP)
    (physicalScalarPack M J N target.length exponent F Q R (localOnlineMassBound M P H)
      (physicalFamilyDraw target N P F exponent H Q passes copies draw pass copy))

noncomputable def physicalFamilySeed (initial : PhysicalEntry M J target.length → ℕ) :
    ℕ → PhysicalEntry M J target.length → ℕ
  | 0 => initial
  | pass + 1 => fun state => min N (upperMedian (List.ofFn fun copy : Fin copies =>
      ⌈(multiplier pass : ℚ) * physicalLocalJointValue source target
        (physicalFamilySeed initial pass) N P F (factor pass) T exponent H Q tau eta kappa delta
        (physicalFamilySample source target N P F exponent H Q T passes copies factor tau hP draw
          (physicalFamilySeed initial pass) pass copy.val) state.1 S state.2⌉₊))

noncomputable def physicalFamilyGroup (pass copy : ℕ) :=
  physicalRawGroupDraws M J N target.length exponent F Q R
    (fun group => physicalScalarPack M J N target.length exponent F Q R (localOnlineMassBound M P H)
      (physicalFamilyDraw target N P F exponent H Q passes copies draw pass copy) (.inr group))

noncomputable def physicalFamilyInteger (initial : PhysicalEntry M J target.length → ℕ)
    (pass copy : ℕ) :=
  physicalRawOnlineIntegers source target
    (physicalFamilySeed source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta hP draw initial pass)
    N P F (factor pass) T exponent H tau
    (fun online => physicalFamilySample source target N P F exponent H Q T passes copies factor tau hP draw
      (physicalFamilySeed source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta hP draw initial pass) pass copy (.inl online))

 theorem physicalFamilySeed_eq (initial : PhysicalEntry M J target.length → ℕ) (pass : ℕ) :
    localSeedSequence source target N P F exponent H Q T S copies factor multiplier tau eta kappa delta
      (physicalFamilyGroup target N P F exponent H Q passes copies draw)
      (physicalFamilyInteger source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta hP draw initial) initial pass =
    physicalFamilySeed source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta hP draw initial pass := by
  induction pass with
  | zero => rfl
  | succ pass ih =>
    rw [localSeedSequence, physicalFamilySeed, ih]
    rfl

omit [DecidableEq α] [NeZero R] in
 theorem physicalFamilyGroupRead_value (pass copy : ℕ) (node : PhysicalInternalNode M J)
    (time : Fin R) (key : GroupScalarKey M F Q) :
    (physicalFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).value
      (physicalFamilyAnswer target N P F exponent H Q passes copies draw) =
    groupScalarValue (physicalFamilyGroup target N P F exponent H Q passes copies draw pass copy node time) key := by
  rw [physicalFamilyGroupRead, FiniteQuery.mapKeys_value]
  exact physicalScalarGroupRead_value M J N target.length exponent F Q R (localOnlineMassBound M P H)
    (physicalFamilyDraw target N P F exponent H Q passes copies draw pass copy) node time key

 theorem physicalFamilyOnlineRead_value (initial : PhysicalEntry M J target.length → ℕ)
    (pass copy : ℕ) (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval target.length) :
    (physicalFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key
      (keyedOnlineSourceRange source target (physicalSourceInterval source.length node.val) P exponent H tau
        (fun i r => (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S copies
          factor multiplier tau eta kappa delta
          (physicalFamilyGroup target N P F exponent H Q passes copies draw)
          (physicalFamilyInteger source target N P F exponent H Q T S passes copies factor multiplier
            tau eta kappa delta hP draw initial) initial
          (PhysicalTableRequest.warmup pass copy (physicalChild node.val node.property i) j.val r)) / T) key)).value
      (physicalFamilyAnswer target N P F exponent H Q passes copies draw) =
    (physicalFamilyInteger source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta hP draw initial pass copy node time key.1 key.2 : ℚ) := by
  rw [physicalFamilyOnlineRead, FiniteQuery.mapKeys_value]
  apply physicalScalarOnlineRead_value source target
    (physicalFamilySeed source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta hP draw initial pass) N P F (factor pass) T exponent H Q R
    (localOnlineMassBound M P H) tau
    (physicalLocalOnlineMass_le source target _ N P F (factor pass) T exponent H tau hP)
    (physicalFamilyDraw target N P F exponent H Q passes copies draw pass copy) node time key
  intro hb
  rw [localRequestValue_onlineRange source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta, physicalFamilySeed_eq]

end Family

end EditApproximation

end OAI
