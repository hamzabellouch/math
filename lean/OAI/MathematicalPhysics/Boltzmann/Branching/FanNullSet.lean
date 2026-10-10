import OAI.MathematicalPhysics.Boltzmann.Collision.AnalyticTools
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Nullity of a set whose lines through one point have null sections -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
namespace BoltzmannNonuniqueness.Published

abbrev FanRemainder := Fin 19 → ℝ
abbrev FanPhase := ℝ × FanRemainder

def fan (a : FanPhase) (y : FanRemainder) (t : ℝ) : FanPhase :=
  (a.1+t,a.2+t • y)

theorem fan_null_set (a : FanPhase) {Z : Set FanPhase} (hZ : MeasurableSet Z)
    (hline : ∀ y : FanRemainder, ∀ᵐ t : ℝ, fan a y t ∉ Z) :
    (volume : Measure FanPhase) Z = 0 := by
  have hm : Measurable (fun z : FanRemainder × ℝ => fan a z.1 z.2) := by
    unfold fan
    fun_prop
  have hall : ∀ᵐ z ∂(volume : Measure FanRemainder).prod (volume : Measure ℝ),
      fan a z.1 z.2 ∉ Z := by
    apply (Measure.ae_prod_iff_ae_ae (hZ.preimage hm).compl).mpr
    exact ae_of_all _ hline
  have ht : ∀ᵐ t : ℝ, ∀ᵐ y : FanRemainder, fan a y t ∉ Z := by
    exact Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ))
      (ν := (volume : Measure FanRemainder)) (p := fun z => fan a z.2 z.1 ∉ Z)
      ((Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure FanRemainder))).quasiMeasurePreserving.ae hall)
  have hsections : ∀ᵐ t : ℝ, ∀ᵐ x : FanRemainder, (a.1+t,x) ∉ Z := by
    filter_upwards [ht,volume.ae_ne (0:ℝ)] with t ht htn
    have hp : QuasiMeasurePreserving (fun x : FanRemainder => t⁻¹ • (x-a.2)) volume volume := by
      simpa only [sub_eq_add_neg, Function.comp_def] using
        (Measure.quasiMeasurePreserving_smul (volume : Measure FanRemainder) (inv_ne_zero htn)).comp
          (quasiMeasurePreserving_add_right (volume : Measure FanRemainder) (-a.2))
    filter_upwards [hp.ae ht] with x hx
    simpa only [fan,smul_smul,mul_inv_cancel₀ htn,one_smul,add_sub_cancel] using hx
  have htranslated : ∀ᵐ t : ℝ, ∀ᵐ x : FanRemainder, (t,x) ∉ Z := by
    have hp := (quasiMeasurePreserving_add_right (volume : Measure ℝ) (-a.1)).ae hsections
    simpa [add_comm,add_left_comm,add_assoc] using hp
  have hfinal : ∀ᵐ z : FanPhase, z ∉ Z := by
    rw [Measure.volume_eq_prod]
    exact (Measure.ae_prod_iff_ae_ae hZ.compl).mpr htranslated
  simpa using ae_iff.mp hfinal

end BoltzmannNonuniqueness.Published

end

end OAI
