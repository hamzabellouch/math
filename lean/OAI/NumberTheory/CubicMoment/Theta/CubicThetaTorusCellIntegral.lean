import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPeriodMeasure

namespace OAI

/-! Haar integration on the cusp torus agrees with the actual half-open
level-three cell, including its boundary convention and Jacobian. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

local instance cubicThetaTorusCellMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

lemma cubicThetaCube_halfOpen_measure :
    (volume : Measure (Fin 2 → ℝ)).restrict {x | ∀ i, x i∈Ico (0:ℝ) 1}=
      (volume : Measure (Fin 2 → ℝ)).restrict {x | ∀ i, x i∈Ioc (0:ℝ) 1} := by
  have hco := Measure.restrict_pi_pi (fun _ : Fin 2 => (volume : Measure ℝ))
    (fun _ => Ico (0:ℝ) 1)
  have hoc := Measure.restrict_pi_pi (fun _ : Fin 2 => (volume : Measure ℝ))
    (fun _ => Ioc (0:ℝ) 1)
  have he : (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Ico (0:ℝ) 1))=
      (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Ioc (0:ℝ) 1)) := by
    funext i
    exact restrict_Ico_eq_restrict_Ioc
  have hm := hco.trans ((congrArg Measure.pi he).trans hoc.symm)
  have hcoSet : (univ.pi (fun _ : Fin 2 => Ico (0:ℝ) 1))=
      {x | ∀ i, x i∈Ico (0:ℝ) 1} := by ext x; simp
  have hocSet : (univ.pi (fun _ : Fin 2 => Ioc (0:ℝ) 1))=
      {x | ∀ i, x i∈Ioc (0:ℝ) 1} := by ext x; simp
  rw [hcoSet,hocSet] at hm
  exact hm

lemma cubicThetaTorus_integral_cell (f : UnitAddTorus (Fin 2) → ℂ) :
    (∫ t, f t)=∫ x in {x : Fin 2 → ℝ | ∀ i, x i∈Ico (0:ℝ) 1},
      f (fun i => (x i:UnitAddCircle)) := by
  rw [cubicThetaCube_halfOpen_measure]
  simpa only [Pi.zero_apply,zero_add] using UnitAddTorus.integral_preimage f (0 : Fin 2 → ℝ)

end CubicFirstMoment

end

end OAI
