import OAI.Combinatorics.EditApproximation.Refinement.PhysicalScalarFamily

namespace OAI

/-! Regrouping the finite physical scalar source gives exactly one fresh
common draw for each pass and copy. This is equality of product laws,
not an assumption about the sampler. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

 theorem finite_pi_product_curry {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : κ → Type*} [∀ j, Fintype (X j)] [∀ j, MeasurableSpace (X j)]
    [∀ j, MeasurableSingletonClass (X j)] (μ : ∀ j, Measure (X j))
    [∀ j, IsProbabilityMeasure (μ j)] :
    (Measure.pi fun pair : ι × κ => μ pair.2).map (fun draw i j => draw (i, j)) =
      Measure.pi fun _ : ι => Measure.pi μ := by
  classical
  apply Measure.ext_of_singleton
  intro result
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hpre : (fun draw i j => draw (i, j)) ⁻¹' {result} =
      {fun pair : ι × κ => result pair.1 pair.2} := by
    ext draw
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext pair
      exact congrFun (congrFun h pair.1) pair.2
    · rintro rfl
      rfl
  rw [hpre]
  simp only [Measure.pi_singleton]
  simpa only [Finset.univ_product_univ] using
    (Finset.prod_product (Finset.univ : Finset ι) (Finset.univ : Finset κ)
      (fun pair => μ pair.2 {result pair.1 pair.2}))

section FamilyLaw

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)

local notation "Key" => PhysicalScalarKey M J N target.length exponent F Q R (localOnlineMassBound M P H)
local notation "range" => physicalScalarRange M J N target.length exponent F Q R (localOnlineMassBound M P H)

noncomputable def physicalFamilyLaw : Measure (PhysicalFamilyScalarDraw
    (M := M) (J := J) (R := R) target N P F exponent H Q passes copies) :=
  Measure.pi fun key => (PMF.uniformOfFintype (Fin (range key.2.2))).toMeasure

instance physicalFamilyLaw_probability : IsProbabilityMeasure
    (physicalFamilyLaw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies) := by
  unfold physicalFamilyLaw
  infer_instance

def physicalFamilyCurry (draw : PhysicalFamilyScalarDraw
    (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    (pass : Fin (passes + 1)) (copy : Fin (copies + 1)) :
    PhysicalScalarDraw M J N target.length exponent F Q R (localOnlineMassBound M P H) :=
  fun key => draw (pass, copy, key)

 theorem physicalFamilyCurry_law :
    (physicalFamilyLaw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies).map
      (physicalFamilyCurry target N P F exponent H Q passes copies) =
    Measure.pi fun _ : Fin (passes + 1) => Measure.pi fun _ : Fin (copies + 1) =>
      physicalScalarLaw M J N target.length exponent F Q R (localOnlineMassBound M P H) := by
  let μ : ∀ key : Key, Measure (Fin (range key)) := fun key =>
    (PMF.uniformOfFintype (Fin (range key))).toMeasure
  have hfirst := finite_pi_product_curry (ι := Fin (passes + 1))
    (κ := Fin (copies + 1) × Key) (fun pair => μ pair.2)
  have hsecond := Measure.pi_map_pi
    (μ := fun _ : Fin (passes + 1) => Measure.pi fun pair : Fin (copies + 1) × Key => μ pair.2)
    (f := fun (_ : Fin (passes + 1)) draw (copy : Fin (copies + 1)) (key : Key) => draw (copy, key))
    (fun _ => (measurable_of_finite _).aemeasurable)
  have hrow := finite_pi_product_curry (ι := Fin (copies + 1)) μ
  have htarget : (Measure.pi fun _ : Fin (passes + 1) =>
      (Measure.pi fun pair : Fin (copies + 1) × Key => μ pair.2).map
        (fun draw copy key => draw (copy, key))) =
      Measure.pi fun _ : Fin (passes + 1) => Measure.pi fun _ : Fin (copies + 1) => Measure.pi μ := by
    simp only [hrow]
  rw [← hfirst, Measure.map_map (by fun_prop) (by fun_prop)] at hsecond
  exact hsecond.trans htarget

def physicalFamilyPack (draw : PhysicalFamilyScalarDraw
    (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    (pass : Fin (passes + 1)) (copy : Fin (copies + 1)) :=
  physicalScalarPack M J N target.length exponent F Q R (localOnlineMassBound M P H)
    (physicalFamilyCurry target N P F exponent H Q passes copies draw pass copy)

 theorem physicalFamilyPack_law :
    (physicalFamilyLaw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies).map
      (physicalFamilyPack target N P F exponent H Q passes copies) =
    Measure.pi fun _ : Fin (passes + 1) => Measure.pi fun _ : Fin (copies + 1) =>
      physicalCommonLaw M J N target.length exponent F Q R (localOnlineMassBound M P H) := by
  let pack := physicalScalarPack M J N target.length exponent F Q R (localOnlineMassBound M P H)
  have hrow := Measure.pi_map_pi
    (μ := fun _ : Fin (copies + 1) => physicalScalarLaw M J N target.length exponent F Q R (localOnlineMassBound M P H))
    (f := fun _ => pack) (fun _ => (measurable_of_finite _).aemeasurable)
  have hrow' : (Measure.pi fun _ : Fin (copies + 1) =>
      physicalScalarLaw M J N target.length exponent F Q R (localOnlineMassBound M P H)).map
      (fun row copy => pack (row copy)) =
      Measure.pi fun _ : Fin (copies + 1) =>
        physicalCommonLaw M J N target.length exponent F Q R (localOnlineMassBound M P H) := by
    exact hrow.trans (by simp only [pack, physicalScalarPack_law])
  have h := Measure.pi_map_pi
    (μ := fun _ : Fin (passes + 1) => Measure.pi fun _ : Fin (copies + 1) =>
      physicalScalarLaw M J N target.length exponent F Q R (localOnlineMassBound M P H))
    (f := fun _ row copy => pack (row copy)) (fun _ => (measurable_of_finite _).aemeasurable)
  rw [← physicalFamilyCurry_law target N P F exponent H Q passes copies,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h.trans (by simp only [hrow'])

end FamilyLaw

end EditApproximation

end OAI
