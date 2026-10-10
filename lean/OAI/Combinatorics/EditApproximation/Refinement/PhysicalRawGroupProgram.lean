import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalGroupKeys
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalGroupProgram

namespace OAI

/-! Whole-cell draws are read by their bounded scale and endpoint keys.
No list of all representatives or cells is searched by the provider. -/

namespace EditApproximation

theorem physicalScaleIndex_of_get (N : ℕ) (scale : Fin (dyadicScales N).length) :
    physicalScaleIndex N ((dyadicScales N).get scale) (List.get_mem _ scale) = scale := by
  apply (dyadicScales_nodup N).injective_get
  exact physicalScaleIndex_get N _ _

theorem dependentKeyTransport {ι κ : Type*} (label : ι → κ) (family : κ → Type*)
    (value : ∀ index, family (label index)) (first second : ι)
    (heq : first = second) (hlabel : label first = label second) :
    Eq.mp (congrArg family hlabel) (value first) = value second := by
  subst second
  rfl

section Raw

variable (M J N n exponent F Q R : ℕ) [NeZero M]
  (draw : ∀ key : PhysicalLocalGroupKey M J N n exponent,
    PhysicalLocalGroupArray M J N n exponent F Q R key)

def physicalRawGroupDraws (node : PhysicalInternalNode M J) (time : Fin R) :
    CellGroupDraws M F Q :=
  fun b cell =>
    if hb : b ∈ dyadicScales N then
      if hc : cell.1 ≤ n * 2 ^ exponent ∧ cell.2 ≤ n * 2 ^ exponent then
        let key : PhysicalLocalGroupKey M J N n exponent :=
          (node, physicalScaleIndex N b hb,
            ⟨cell.1, Nat.lt_succ_of_le hc.1⟩, ⟨cell.2, Nat.lt_succ_of_le hc.2⟩)
        Eq.mp (congrArg (fun b => ParentGroupDraw M (groupDyadicScales M b F).length
          (fun h => groupSampleCount M Q b (groupDyadicScaleAt M b F h)))
          (physicalScaleIndex_get N b hb)) (draw key time)
      else fun _ _ => 0
    else fun _ _ => 0

end Raw

section Agreement

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q : ℕ) (A : ℚ)
  (draw : ∀ key : PhysicalLocalGroupKey M J N target.length exponent,
    PhysicalLocalGroupArray M J N target.length exponent F Q R key)

theorem physicalRawGroupDraws_get
    (key : PhysicalGroupKey source target U N P F A exponent) (time : Fin R) :
    physicalRawGroupDraws M J N target.length exponent F Q R draw key.1 time
        ((dyadicScales N).get key.2.1)
        ((physicalProgramCells source target U N P F A exponent key.1.1
          ((dyadicScales N).get key.2.1)).get key.2.2) =
      draw (physicalGroupRawKey source target U N P F exponent A key) time := by
  have hcell := physicalProgramCells_bounds source target U N P F exponent A key.1.1
    ((dyadicScales N).get key.2.1) (physicalGroupScale_positive source target U N P F exponent A key)
    _ (List.get_mem _ key.2.2)
  simp only [physicalRawGroupDraws, dite_eq_left (List.get_mem _ key.2.1), dite_eq_left hcell]
  exact dependentKeyTransport (fun scale => (dyadicScales N).get scale)
    (fun b => ParentGroupDraw M (groupDyadicScales M b F).length
      (fun h => groupSampleCount M Q b (groupDyadicScaleAt M b F h)))
    (fun scale => draw (key.1, scale,
      ⟨_, Nat.lt_succ_of_le hcell.1⟩, ⟨_, Nat.lt_succ_of_le hcell.2⟩) time)
    _ key.2.1 (physicalScaleIndex_of_get N key.2.1)
    (physicalScaleIndex_get N _ (List.get_mem _ key.2.1))

theorem physicalGroupStreamsOfRaw :
    physicalGroupStreamsOfKeys source target U N P F exponent Q A
        (physicalRawGroupDraws M J N target.length exponent F Q R draw) =
      fun node scale cell => draw
        (physicalGroupRawKey source target U N P F exponent A ⟨node, scale, cell⟩) := by
  funext node scale cell time
  exact physicalRawGroupDraws_get source target U N P F exponent Q A draw ⟨node, scale, cell⟩ time

end Agreement

end EditApproximation

end OAI
