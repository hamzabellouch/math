import OAI.MathematicalPhysics.Boltzmann.Admissibility
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarriers

namespace OAI

/-! # A centered fundamental cube for the periodic spatial variable -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusChart

def interval : Set ℝ := Ioc (-(1 / 2 : ℝ)) (1 / 2)

def cube : Set Velocity := {x | ∀ i, x i ∈ interval}

def coordinate (x : AddCircle (1 : ℝ)) : ℝ :=
  ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) x : ℝ)

def representative (x : Position) : Velocity := WithLp.toLp 2 (fun i => coordinate (x i))

theorem coordinate_measurePreserving : MeasurePreserving coordinate volume (volume.restrict interval) := by
  have h := (measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
    (s := Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)) measurableSet_Ioc).comp
    (AddCircle.measurePreserving_equivIoc (T := (1 : ℝ)) (a := -(1 / 2 : ℝ)))
  change MeasurePreserving (Subtype.val ∘ (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))))
    volume (volume.restrict interval)
  have he : Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) = interval := by norm_num [interval]
  rw [← he]
  exact h

theorem measurableSet_cube : MeasurableSet cube := by
  have he : cube = ⋂ i : Fin 3, {x : Velocity | x i ∈ interval} := by ext x; simp [cube]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_Ioc.preimage
    (show Measurable (fun x : Velocity => x i) from (PiLp.continuous_apply 2 _ i).measurable))

theorem representative_measurePreserving :
    MeasurePreserving representative volume (volume.restrict cube) := by
  have hp := measurePreserving_pi (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ : Fin 3 => (volume : Measure ℝ).restrict interval) (fun _ => coordinate_measurePreserving)
  have he := (PiLp.volume_preserving_toLp (ι := Fin 3)).restrict_preimage measurableSet_cube
  have hpre : WithLp.toLp 2 ⁻¹' cube = Set.univ.pi (fun _ : Fin 3 => interval) := by
    ext x
    simp [cube, Set.mem_pi, interval]
  rw [hpre] at he
  change MeasurePreserving (WithLp.toLp 2)
    ((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict (Set.univ.pi (fun _ => interval)))
    (volume.restrict cube) at he
  rw [Measure.restrict_pi_pi] at he
  exact he.comp hp

theorem representative_mem (x : Position) : representative x ∈ cube := by
  intro i
  have h := ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) (x i)).property
  change -(1 / 2 : ℝ) < coordinate (x i) ∧ coordinate (x i) ≤ 1 / 2
  constructor
  · exact h.1
  · change ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) (x i) : ℝ) ≤ 1 / 2
    linarith [h.2]

theorem projection_representative (x : Position) : torusProjection (representative x) = x := by
  funext i
  exact AddCircle.coe_equivIoc

theorem representative_projection {x : Velocity} (hx : x ∈ cube) :
    representative (torusProjection x) = x := by
  ext i
  have hi : x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
    ⟨(hx i).1, by have := (hx i).2; linarith⟩
  change ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIoc_coe_eq hi]

def phaseRepresentative (p : Phase) : Velocity × Velocity := (representative p.1, p.2)

theorem phase_measurePreserving : MeasurePreserving phaseRepresentative
    (volume : Measure Phase) ((volume : Measure (Velocity × Velocity)).restrict (cube ×ˢ univ)) := by
  change MeasurePreserving phaseRepresentative
    ((volume : Measure Position).prod (volume : Measure Velocity))
    (((volume : Measure Velocity).prod (volume : Measure Velocity)).restrict (cube ×ˢ univ))
  rw [← Measure.prod_restrict]
  have h := representative_measurePreserving.prod (MeasurePreserving.id (volume : Measure Velocity))
  simp only [Measure.restrict_univ]
  convert! h using 1

end BoltzmannNonuniqueness.TorusChart

end

end OAI
