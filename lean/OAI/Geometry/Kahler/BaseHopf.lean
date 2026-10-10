import OAI.Geometry.Kahler.BasePotentialControl

namespace OAI

universe uKahler10884_1 uKahler10884_2 uKahler10889_1 uKahler10889_2 uKahler10889_3

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

instance : MeasurableSpace Circle := borel Circle
instance : BorelSpace Circle := ⟨rfl⟩

def circleMeasure : Measure Circle :=
  Measure.haarMeasure (⟨⟨univ,isCompact_univ⟩,by simp⟩ : TopologicalSpace.PositiveCompacts Circle)

instance : IsProbabilityMeasure circleMeasure where
  measure_univ := Measure.haarMeasure_self
instance : Measure.IsHaarMeasure circleMeasure := inferInstanceAs (Measure.IsHaarMeasure (Measure.haarMeasure _))

def torusMeasure : Measure (Circle × Circle) := circleMeasure.prod circleMeasure
instance : IsProbabilityMeasure torusMeasure := inferInstanceAs (IsProbabilityMeasure (circleMeasure.prod circleMeasure))
instance : Measure.IsMulLeftInvariant torusMeasure := inferInstanceAs (Measure.IsMulLeftInvariant (circleMeasure.prod circleMeasure))
instance : Measure.IsMulRightInvariant torusMeasure := inferInstanceAs (Measure.IsMulRightInvariant (circleMeasure.prod circleMeasure))

def torusAction (z : Circle × Circle) (ξ : Sphere) : Sphere :=
  sphereAction (diagIsometry z.1 z.2 z.1.norm_coe z.2.norm_coe) ξ

@[simp] lemma torusAction_zero (z : Circle × Circle) (ξ : Sphere) :
    (torusAction z ξ : Base) 0 = (z.1:ℂ)*(ξ:Base) 0 := by simp [torusAction]
@[simp] lemma torusAction_one (z : Circle × Circle) (ξ : Sphere) :
    (torusAction z ξ : Base) 1 = (z.2:ℂ)*(ξ:Base) 1 := by simp [torusAction]

lemma torusAction_continuous : Continuous (fun p : (Circle × Circle) × Sphere => torusAction p.1 p.2) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : (Circle × Circle) × Sphere => (torusAction p.1 p.2 : Base) 0)
    simp_rw [torusAction_zero]
    fun_prop
  · change Continuous (fun p : (Circle × Circle) × Sphere => (torusAction p.1 p.2 : Base) 1)
    simp_rw [torusAction_one]
    fun_prop

lemma torusAction_mul (z w : Circle × Circle) (ξ : Sphere) :
    torusAction z (torusAction w ξ) = torusAction (z*w) ξ := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [mul_assoc]

def radialSphere (u : unitInterval) : Sphere :=
  ⟨(WithLp.toLp 2 ![(Real.sqrt (u:ℝ):ℂ),(Real.sqrt (1-(u:ℝ)):ℂ)] : Base),by
    rw [Metric.mem_sphere,dist_zero_right]
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt u.property.1,Real.sq_sqrt (sub_nonneg.mpr u.property.2),one_pow]
    ring⟩

@[simp] lemma radialSphere_zero (u : unitInterval) : (radialSphere u : Base) 0 = (Real.sqrt (u:ℝ):ℂ) := rfl
@[simp] lemma radialSphere_one (u : unitInterval) : (radialSphere u : Base) 1 = (Real.sqrt (1-(u:ℝ)):ℂ) := rfl

lemma radialSphere_continuous : Continuous radialSphere := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [] <;> fun_prop

attribute [irreducible] torusAction radialSphere

def hopf (p : unitInterval × (Circle × Circle)) : Sphere := torusAction p.2 (radialSphere p.1)
lemma hopf_continuous : Continuous hopf :=
by
  unfold hopf
  exact torusAction_continuous.comp (continuous_snd.prodMk (radialSphere_continuous.comp continuous_fst))

lemma exists_circle_norm_factor (z : ℂ) : ∃ a : Circle, (a:ℂ)*(‖z‖:ℂ) = z := by
  by_cases hz : z = 0
  · subst z; exact ⟨1,by simp⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨⟨z/(‖z‖:ℂ),?_⟩,?_⟩
  · apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self hn]
  · exact div_mul_cancel₀ z (by exact_mod_cast hn)

lemma exists_hopf (ξ : Sphere) : ∃ z : Circle × Circle, torusAction z (radialSphere (radialUnit ξ)) = ξ := by
  obtain ⟨a,ha⟩ := exists_circle_norm_factor ((ξ:Base) 0)
  obtain ⟨b,hb⟩ := exists_circle_norm_factor ((ξ:Base) 1)
  refine ⟨(a,b),?_⟩
  apply Subtype.ext
  ext i
  fin_cases i
  · simpa [radialUnit,radialU,Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)] using ha
  · have hv : 1-radialU ξ = radialV ξ := by linarith [radialUV ξ]
    change (torusAction (a,b) (radialSphere (radialUnit ξ)) : Base) 1 = (ξ:Base) 1
    rw [torusAction_one,radialSphere_one]
    change (b:ℂ)*(Real.sqrt (1-radialU ξ):ℂ) = (ξ:Base) 1
    rw [hv,radialV,Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
    exact hb

lemma compact_continuous_integrable {X : Type uKahler10884_1} {E : Type uKahler10884_2} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma continuous_compact_integral {X : Type uKahler10889_1} {Y : Type uKahler10889_2} {E : Type uKahler10889_3} [TopologicalSpace X] [CompactSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E] {μ : Measure Y} [IsFiniteMeasure μ]
    {F : X × Y → E} (hF : Continuous F) : Continuous (fun x => ∫ y, F (x,y) ∂μ) := by
  obtain ⟨C,hC⟩ := isCompact_univ.bddAbove_image hF.norm.continuousOn
  apply continuous_of_dominated
    (fun x => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun x => Eventually.of_forall (fun y => hC (mem_image_of_mem _ (mem_univ _))))
    (integrable_const C)
  exact Eventually.of_forall (fun y => hF.comp (continuous_id.prodMk continuous_const))

lemma hopf_integral (f : C(Sphere,ℝ)) :
    (∫ ξ, f ξ ∂sigma) = ∫ u : unitInterval, ∫ z, f (hopf (u,z)) ∂torusMeasure := by
  let A (ξ : Sphere) := ∫ z, f (torusAction z ξ) ∂torusMeasure
  have hc : Continuous A := continuous_compact_integral
    (f.continuous.comp (torusAction_continuous.comp continuous_swap))
  have havg : (∫ ξ, A ξ ∂sigma) = ∫ ξ, f ξ ∂sigma := by
    rw [show (∫ ξ, A ξ ∂sigma) = ∫ z, ∫ ξ, f (torusAction z ξ) ∂sigma ∂torusMeasure from
      integral_integral_swap (compact_continuous_integrable (f.continuous.comp (torusAction_continuous.comp continuous_swap)))]
    simp only [torusAction,sigma_integral_unitary]
    simp
  have hA : ∀ ξ, A ξ = A (radialSphere (radialUnit ξ)) := by
    intro ξ
    obtain ⟨w,hw⟩ := exists_hopf ξ
    conv_lhs => rw [← hw]
    simp only [A,torusAction_mul]
    exact integral_mul_right_eq_self (fun z => f (torusAction z (radialSphere (radialUnit ξ)))) w
  rw [← havg]
  calc
    _ = ∫ ξ, A (radialSphere (radialUnit ξ)) ∂sigma := integral_congr_ae (Eventually.of_forall hA)
    _ = _ := radial_continuous_integral ⟨A ∘ radialSphere,hc.comp radialSphere_continuous⟩

end PinchedHartogs.BaseConstruction

end

end OAI
