import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

section

/-! # Measurability of a parameter-dependent interval primitive -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive
variable {P : Type*} [MeasurableSpace P]

theorem measurable_interval_primitive {f : ℝ × P → ℝ} (hf : Measurable f) :
    Measurable (fun z : ℝ × P => ∫ s in 0..z.1, f (s,z.2)) := by
  have hm : Measurable (fun q : (ℝ × P) × ℝ => f (q.2,q.1.2)) :=
    hf.comp (measurable_snd.prodMk measurable_fst.snd)
  have hplus : Measurable (fun q : (ℝ × P) × ℝ =>
      if 0 < q.2 ∧ q.2 ≤ q.1.1 then f (q.2,q.1.2) else 0) :=
    hm.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst)) measurable_const
  have hminus : Measurable (fun q : (ℝ × P) × ℝ =>
      if q.1.1 < q.2 ∧ q.2 ≤ 0 then f (q.2,q.1.2) else 0) :=
    hm.ite ((measurableSet_lt measurable_fst.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) measurable_const
  have hp := (hplus.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hn := (hminus.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hp.sub hn using 1
  funext z
  change (∫ s in Ioc 0 z.1, f (s,z.2))-(∫ s in Ioc z.1 0, f (s,z.2)) = _
  rw [← integral_indicator measurableSet_Ioc,← integral_indicator measurableSet_Ioc]
  simp only [Set.indicator,mem_Ioc,Pi.sub_apply]

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Measurability of the exact transport resolvent and its velocity averages -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Published

theorem transportResolvent_measurable {r : KineticPhase → ℝ} (hr : Measurable r) :
    Measurable (transportResolvent r) := by
  have hm : Measurable (fun p : KineticPhase × ℝ =>
      Real.exp (-p.2)*r ((p.1.1.1-p.2,p.1.1.2-p.2 • p.1.2),p.1.2)) := by
    exact (by fun_prop : Measurable (fun p : KineticPhase × ℝ => Real.exp (-p.2))).mul
      (hr.comp (by fun_prop))
  exact hm.stronglyMeasurable.integral_prod_right.measurable

theorem resolventAverage_measurable {r : KineticPhase → ℝ} (hr : Measurable r)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) : Measurable (resolventAverage r ψ) :=
  ((hψ.comp measurable_snd).mul (transportResolvent_measurable hr)).stronglyMeasurable.integral_prod_right.measurable

end BoltzmannNonuniqueness.Published

end

end

end OAI
