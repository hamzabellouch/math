import OAI.Dynamics.EntropyCounterexample.ClockRotation
import OAI.Dynamics.EntropyCounterexample.ClockModel

namespace OAI

noncomputable section

namespace Problem340.Clock

lemma clockHomeomorph_val_real (t : ℝ) :
    (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))).val = parametrization t := by
  ext i
  fin_cases i
  · change (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))).val 0 =
      Real.cos (2 * Real.pi * t / 100)
    simp [ClockModel.clockHomeomorph, Homeomorph.trans_apply,
      AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_apply_mk, Circle.coe_exp, Complex.exp_re]
    congr 1
    ring
  · change (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))).val 1 =
      Real.sin (2 * Real.pi * t / 100)
    simp [ClockModel.clockHomeomorph, Homeomorph.trans_apply,
      AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_apply_mk, Circle.coe_exp, Complex.exp_im]
    congr 1
    ring

lemma ambientBarrier_clockHomeomorph (t : ℝ) :
    ambientBarrier (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))).val = barrier t := by
  rw [clockHomeomorph_val_real]
  exact ambientBarrier_on_circle t (parametrization t) rfl

lemma update_clockHomeomorph_real (t e : ℝ) :
    update (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))) e =
      ClockModel.clockHomeomorph ((t + increment t e : ℝ) : AddCircle (100 : ℝ)) := by
  apply Subtype.ext
  change ambientUpdate _ e = _
  rw [clockHomeomorph_val_real, clockHomeomorph_val_real, ambientUpdate_parametrization]

lemma update_clockHomeomorph (t : AddCircle (100 : ℝ)) (e : ℝ) :
    update (ClockModel.clockHomeomorph t) e =
      ClockModel.clockHomeomorph
        (t + (ambientIncrement (ClockModel.clockHomeomorph t).val e : ℝ)) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hi : ambientIncrement (ClockModel.clockHomeomorph (t : AddCircle (100 : ℝ))).val e =
      increment t e := by
    rw [clockHomeomorph_val_real]
    exact ambientIncrement_parametrization t e
  rw [hi]
  exact update_clockHomeomorph_real t e

end Problem340.Clock

end

end OAI
