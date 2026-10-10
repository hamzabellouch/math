import OAI.Probability.FreeIsing.Estimates.UniformTwist
import OAI.Probability.FreeIsing.Trees.RootedBroadcast

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem measurePreserving_fairSpin_mul (b : IsingSpin) :
    MeasurePreserving (fun a => spinMul a b)
      (uniform01.map fairSpin) (uniform01.map fairSpin) := by
  have hm : Measurable (fun a => spinMul a b) := measurable_of_finite _
  refine ⟨hm, ?_⟩
  apply Measure.ext_of_singleton
  intro a
  have hpre : (fun x => spinMul x b) ⁻¹' {a} = {spinMul a b} := by
    ext x
    cases x <;> cases a <;> cases b <;> simp [spinMul]
  rw [Measure.map_apply hm (measurableSet_singleton a), hpre,
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _),
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass,
    fairSpin_mass]

theorem measurePreserving_fairSpin_twist
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {f : Y → IsingSpin} (hf : Measurable f) :
    MeasurePreserving (fun p : IsingSpin × Y => (spinMul p.1 (f p.2), p.2))
      ((uniform01.map fairSpin).prod ν) ((uniform01.map fairSpin).prod ν) := by
  apply measurePreserving_fiberTwist (uniform01.map fairSpin) ν
    (fun y a => spinMul a (f y))
  · exact measurable_spinMul.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  · intro y
    exact measurePreserving_fairSpin_mul (f y)

theorem map_pair_spinMul_of_indepFun
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (P : Measure Ω) [IsFiniteMeasure P]
    {B : Ω → IsingSpin} {Z : Ω → Y} {f : Y → IsingSpin}
    (hB : Measurable B) (hZ : Measurable Z) (hf : Measurable f)
    (hfair : P.map B = uniform01.map fairSpin) (hind : IndepFun B Z P) :
    P.map (fun ω => (spinMul (B ω) (f (Z ω)), Z ω)) =
      (uniform01.map fairSpin).prod (P.map Z) := by
  rw [← hfair]
  apply map_pair_fiberTwist_of_indepFun P hB hZ hind (fun z b => spinMul b (f z))
  · exact measurable_spinMul.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  · intro z
    rw [hfair]
    exact measurePreserving_fairSpin_mul (f z)

end RootedBroadcast
end Problem367

end

end OAI
