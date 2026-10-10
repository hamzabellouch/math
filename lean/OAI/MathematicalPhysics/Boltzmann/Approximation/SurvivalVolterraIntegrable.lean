import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakConservedMarginal

namespace OAI

section

/-! # Measurability of a survival-weighted characteristic source -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P] {μ : Measure ℝ} [SFinite μ]

theorem survivalVolterra_measurable {a : (ℝ × P) × ℝ → ℝ} {f : ℝ × P → ℝ}
    (ha : Measurable a) (hf : Measurable f) : Measurable (survivalVolterra μ a f) := by
  have hm : Measurable (fun z : (ℝ × P) × ℝ =>
      if z.2 ≤ z.1.1 then a z*f (z.2,z.1.2) else 0) :=
    (ha.mul (hf.comp (measurable_snd.prodMk measurable_fst.snd))).ite
      (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Integrability of a bounded survival kernel against an integrable source -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

theorem survivalVolterra_integrable {f : ℝ × P → ℝ} {a : (ℝ × P) × ℝ → ℝ}
    (hf : Integrable f (μ.prod ν)) (ha : Measurable a) (C : ℝ) (hC : ∀ z, |a z| ≤ C) :
    Integrable (survivalVolterra μ a f) (μ.prod ν) := by
  have hi : Integrable (fun z : (ℝ × P) × ℝ => f (z.2,z.1.2)) ((μ.prod ν).prod μ) :=
    (timeExchange_measurePreserving μ ν).integrable_comp_of_integrable (hf.comp_fst μ)
  have hai := hi.bdd_mul ha.aestronglyMeasurable (ae_of_all _ hC)
  let k : (ℝ × P) × ℝ → ℝ := fun z => if z.2 ≤ z.1.1 then 1 else 0
  have hkm : Measurable k := measurable_const.ite
    (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  have hkb : ∀ z, |k z| ≤ 1 := by intro z; dsimp [k]; split <;> norm_num
  have h := (hai.bdd_mul hkm.aestronglyMeasurable (ae_of_all _ hkb)).integral_prod_left
  convert h using 1
  funext z
  apply integral_congr_ae
  filter_upwards [] with s
  dsimp only [survivalVolterra,k]
  split <;> simp

end BoltzmannNonuniqueness.Published

end

end

end OAI
