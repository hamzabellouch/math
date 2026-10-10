import OAI.Dynamics.TriangleBilliards.MeasurableFlow

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section

namespace TriangularBilliards

local instance anglePeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Angular Haar probability in additive angle coordinates, used to
verify invariance of the explicit angular measure. -/
def angleMeasure : Measure (AddCircle (2 * Real.pi)) :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume

lemma measurePreserving_toCircle :
    MeasurePreserving (AddCircle.homeomorphCircle' : AddCircle (2 * Real.pi) → Circle) angleMeasure angularMeasure := by
  have hc : Measurable (fun t : ℝ => (t : AddCircle (2 * Real.pi))) :=
    (AddCircle.measurePreserving_mk (2 * Real.pi) 0).measurable
  have he : Measurable (AddCircle.homeomorphCircle' : AddCircle (2 * Real.pi) → Circle) :=
    AddCircle.homeomorphCircle'.continuous.measurable
  refine ⟨he, ?_⟩
  have hvol := ((AddCircle.measurePreserving_mk (2 * Real.pi) 0).smul_measure
    ((ENNReal.ofReal (2 * Real.pi))⁻¹)).map_eq
  simp only [zero_add] at hvol
  rw [angleMeasure, ← hvol, Measure.map_map he hc]
  rw [angularMeasure, Measure.restrict_congr_set Ico_ae_eq_Ioc]
  rfl

lemma measurePreserving_circle_mul (a : Circle) :
    MeasurePreserving (fun v : Circle => a * v) angularMeasure angularMeasure := by
  let θ : AddCircle (2 * Real.pi) := AddCircle.homeomorphCircle'.symm a
  have hθ : AddCircle.homeomorphCircle' θ = a := AddCircle.homeomorphCircle'.apply_symm_apply a
  have ha := (measurePreserving_add_left (volume : Measure (AddCircle (2 * Real.pi))) θ).smul_measure
    ((ENNReal.ofReal (2 * Real.pi))⁻¹)
  change MeasurePreserving (fun x : AddCircle (2 * Real.pi) => θ + x) angleMeasure angleMeasure at ha
  have hh := measurePreserving_toCircle.comp ha
  have hf : AddCircle.homeomorphCircle' ∘ (fun x : AddCircle (2 * Real.pi) => θ + x) =
      (fun v : Circle => a * v) ∘ AddCircle.homeomorphCircle' := by
    funext x
    exact (Real.Angle.toCircle_add θ x).trans
      (congrArg (fun v : Circle => v * Real.Angle.toCircle x) hθ)
  rw [hf] at hh
  have hr := hh.map_of_comp (by fun_prop) measurePreserving_toCircle.measurable
  rwa [measurePreserving_toCircle.map_eq] at hr

lemma measurePreserving_circle_inv :
    MeasurePreserving (fun v : Circle => v⁻¹) angularMeasure angularMeasure := by
  have hn := (Measure.measurePreserving_neg (volume : Measure (AddCircle (2 * Real.pi)))).smul_measure
    ((ENNReal.ofReal (2 * Real.pi))⁻¹)
  change MeasurePreserving (fun x : AddCircle (2 * Real.pi) => -x) angleMeasure angleMeasure at hn
  have hh := measurePreserving_toCircle.comp hn
  have hf : AddCircle.homeomorphCircle' ∘ (fun x : AddCircle (2 * Real.pi) => -x) =
      (fun v : Circle => v⁻¹) ∘ AddCircle.homeomorphCircle' := by
    funext x
    exact Real.Angle.toCircle_neg x
  rw [hf] at hh
  have hr := hh.map_of_comp (by fun_prop) measurePreserving_toCircle.measurable
  rwa [measurePreserving_toCircle.map_eq] at hr

lemma reflectedDirection_eq (Q : Triangle) (i : Fin 3) (v : Circle) :
    reflectedDirection Q i v = reflectedDirection Q i 1 * v⁻¹ := by
  apply Subtype.ext
  simp only [Circle.coe_mul, Circle.coe_inv_eq_conj]
  simp [reflectedDirection, reflect]

lemma measurePreserving_reflectedDirection (Q : Triangle) (i : Fin 3) :
    MeasurePreserving (reflectedDirection Q i) angularMeasure angularMeasure := by
  convert (measurePreserving_circle_mul (reflectedDirection Q i 1)).comp
    measurePreserving_circle_inv using 1
  funext v
  exact reflectedDirection_eq Q i v

lemma measurePreserving_wallReflection (Q : Triangle) (i : Fin 3) :
    MeasurePreserving (wallReflection Q i) volume volume := by
  have hs := measurePreserving_add_right (volume : Measure ℂ) (-Q.vertex i)
  have hr := (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)).measurePreserving
  have ha := measurePreserving_add_left (volume : Measure ℂ) (Q.vertex i)
  convert ha.comp (hr.comp hs) using 1
  funext x
  simp only [Function.comp_apply, wallReflection, sub_eq_add_neg]
  rfl

/-- Ambient Liouville measure, before restriction and normalization. -/
def ambientMeasure : Measure Phase := volume.prod angularMeasure

/-- Reflection at a whole supporting line, on the ambient phase space. -/
def wallPhase (Q : Triangle) (i : Fin 3) (z : Phase) : Phase :=
  (wallReflection Q i z.1, reflectedDirection Q i z.2)

lemma measurePreserving_wallPhase (Q : Triangle) (i : Fin 3) :
    MeasurePreserving (wallPhase Q i) ambientMeasure ambientMeasure :=
  (measurePreserving_wallReflection Q i).prod (measurePreserving_reflectedDirection Q i)

/-- The free-flight shear on the whole plane, without any boundary. -/
def freeFlow (t : ℝ) (z : Phase) : Phase := (z.1 + t • (z.2 : ℂ), z.2)

lemma measurePreserving_freeFlow (t : ℝ) :
    MeasurePreserving (freeFlow t) ambientMeasure ambientMeasure := by
  have hs : MeasurePreserving (fun z : Circle × ℂ => (z.1, z.2 + t • (z.1 : ℂ)))
      (angularMeasure.prod volume) (angularMeasure.prod volume) := by
    apply (MeasurePreserving.id angularMeasure).skew_product
      (g := fun (v : Circle) (x : ℂ) => x + t • (v : ℂ))
    · fun_prop
    · exact Filter.Eventually.of_forall fun v =>
        (measurePreserving_add_right (volume : Measure ℂ) (t • (v : ℂ))).map_eq
  exact Measure.measurePreserving_swap.comp (hs.comp Measure.measurePreserving_swap)

end TriangularBilliards

end

end OAI
