import OAI.Combinatorics.EditApproximation.Refinement.PhysicalScalarFamilyLaw
import OAI.Combinatorics.EditApproximation.Probability.FiniteArrayMarginal

namespace OAI

/-! The literal finite scalar family supplies the independent common
source trace and its final draw, after removing unused extra copies. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section SourceFamily

variable {Seed α : Type} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)

local notation "Draw" => PhysicalCommonDraw M J N target.length exponent F Q R (localOnlineMassBound M P H)
local notation "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P F exponent H Q passes copies
local notation "μ" => physicalCommonLaw M J N target.length exponent F Q R (localOnlineMassBound M P H)

def physicalFamilyToTrace (input : Seed × Family) :
    CommonSeedTrace Seed (fun _ => Fin copies → Draw) passes × Draw :=
  let packed := physicalFamilyPack target N P F exponent H Q passes copies input.2
  let rows := commonArrayFinal passes (input.1, packed)
  (mapCommonTrace (fun row (copy : Fin copies) => row copy.castSucc) passes rows.1,
    rows.2 0)

variable [Fintype Seed] [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  (incoming : Measure Seed)

 theorem physicalFamilyToTrace_law :
    (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)).map
      (physicalFamilyToTrace (Seed := Seed) target N P F exponent H Q passes copies) =
    (commonTraceLaw (fun _ => Measure.pi fun _ : Fin copies => μ) incoming passes).prod μ := by
  classical
  let : MeasurableSingletonClass Draw := inferInstance
  let : MeasurableSingletonClass (Fin (copies + 1) → Draw) := inferInstance
  let : MeasurableSingletonClass (Fin (passes + 1) → Fin (copies + 1) → Draw) := inferInstance
  let := commonSeedTraceFintype Seed (fun _ => Fin (copies + 1) → Draw) passes
  let := commonSeedTraceSingleton Seed (fun _ => Fin (copies + 1) → Draw) passes
  let rowLaw : Measure (Fin (copies + 1) → Draw) := Measure.pi fun _ => μ
  let trim : (Fin (copies + 1) → Draw) → (Fin copies → Draw) := fun row copy => row copy.castSucc
  let finish : (Fin (copies + 1) → Draw) → Draw := fun row => row 0
  let pack : Seed × Family → Seed × (Fin (passes + 1) → Fin (copies + 1) → Draw) :=
    Prod.map (id : Seed → Seed)
    (physicalFamilyPack target N P F exponent H Q passes copies)
  let finalMap := Prod.map (mapCommonTrace (Seed := Seed) trim passes) finish
  have hpack : (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)).map pack =
      incoming.prod (Measure.pi fun _ : Fin (passes + 1) => rowLaw) := by
    dsimp only [pack, rowLaw]
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_of_finite _), Measure.map_id,
      physicalFamilyPack_law]
  have hrow : rowLaw.map trim = Measure.pi fun _ : Fin copies => μ :=
    finite_init_law μ copies
  have hlast : rowLaw.map finish = μ := by
    simpa only [measure_univ, Finset.prod_const_one, one_smul] using
      (Measure.pi_map_eval (fun _ : Fin (copies + 1) => μ) 0)
  have hmap : ((commonTraceLaw (fun _ => rowLaw) incoming passes).prod rowLaw).map finalMap =
      (commonTraceLaw (fun _ => Measure.pi fun _ : Fin copies => μ) incoming passes).prod μ := by
    dsimp only [finalMap]
    rw [← Measure.map_prod_map _ _ (measurable_of_finite _) (measurable_of_finite _),
      mapCommonTrace_law incoming rowLaw trim passes, hrow, hlast]
  have heq : physicalFamilyToTrace (Seed := Seed) target N P F exponent H Q passes copies =
      finalMap ∘ commonArrayFinal passes ∘ pack := rfl
  rw [heq, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hpack,
    commonArrayFinal_law incoming rowLaw passes]
  exact hmap

end SourceFamily

end EditApproximation

end OAI
