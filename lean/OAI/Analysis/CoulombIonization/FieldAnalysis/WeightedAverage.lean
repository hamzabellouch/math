import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.PhysicalGrid

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter

namespace CoulombNeumann
variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
  {μ : Measure A} {ν : Measure X} [IsProbabilityMeasure μ] [SFinite ν]

lemma bounded_average_section_integrable {P : A → X → ℝ}
    (hm : Measurable (Function.uncurry P)) (hn : ∀ a x, 0 ≤ P a x)
    {B : ℝ} (hb : ∀ a x, P a x ≤ B) (x : X) : Integrable (fun a => P a x) μ := by
  apply (integrable_const B).mono' (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall fun a => by
    change ‖P a x‖ ≤ B
    rw [Real.norm_of_nonneg (hn a x)]
    exact hb a x

lemma bounded_average_joint_integrable {P : A → X → ℝ}
    (hm : Measurable (Function.uncurry P)) (hn : ∀ a x, 0 ≤ P a x)
    {B : ℝ} (hb : ∀ a x, P a x ≤ B) {w : X → ℝ} (hw : Integrable w ν) :
    Integrable (fun p : A × X => P p.1 p.2*w p.2) (μ.prod ν) := by
  have hmi : AEStronglyMeasurable (fun p : A × X => P p.1 p.2*w p.2) (μ.prod ν) :=
    hm.aestronglyMeasurable.mul hw.aestronglyMeasurable.comp_snd
  apply (integrable_prod_iff hmi).mpr
  have hi (a : A) : Integrable (fun x => P a x*w x) ν := by
    apply hw.bdd_mul (c := B) (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by change ‖P a x‖ ≤ B; rw [Real.norm_of_nonneg (hn a x)]; exact hb a x)
  refine ⟨Eventually.of_forall hi,?_⟩
  apply (integrable_const (B*(∫ x, ‖w x‖ ∂ν))).mono' hmi.norm.integral_prod_right'
  exact Eventually.of_forall fun a => by
    change ‖∫ x, ‖P a x*w x‖ ∂ν‖ ≤ B*(∫ x, ‖w x‖ ∂ν)
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),←integral_const_mul]
    apply integral_mono (hi a).norm (hw.norm.const_mul B)
    intro x
    change ‖P a x*w x‖ ≤ B*‖w x‖
    rw [norm_mul,Real.norm_of_nonneg (hn a x)]
    exact mul_le_mul_of_nonneg_right (hb a x) (norm_nonneg _)

theorem weighted_average_fubini {P : A → X → ℝ}
    (hm : Measurable (Function.uncurry P)) (hn : ∀ a x, 0 ≤ P a x)
    {B : ℝ} (hb : ∀ a x, P a x ≤ B) {w : X → ℝ} (hw : Integrable w ν) :
    (∫ x, (∫ a, P a x ∂μ)*w x ∂ν) = ∫ a, (∫ x, P a x*w x ∂ν) ∂μ := by
  simp_rw [←integral_mul_const]
  exact (integral_integral_swap (bounded_average_joint_integrable hm hn hb hw)).symm

theorem weighted_average_bound {P : A → X → ℝ}
    (hm : Measurable (Function.uncurry P)) (hn : ∀ a x, 0 ≤ P a x)
    {B : ℝ} (hb : ∀ a x, P a x ≤ B) {w : X → ℝ} (hw : Integrable w ν)
    {T E : ℝ} (h : ∀ a, T*(∫ x, P a x*w x ∂ν) ≤ E) :
    T*(∫ x, (∫ a, P a x ∂μ)*w x ∂ν) ≤ E := by
  rw [weighted_average_fubini hm hn hb hw,←integral_const_mul]
  exact (integral_mono ((bounded_average_joint_integrable hm hn hb hw).integral_prod_left.const_mul T)
    (integrable_const E) h).trans_eq (by simp)

end CoulombNeumann

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

abbrev CubePartition := CubeRotation × (Fin 3 → I)
def cubePartitionMeasure : Measure CubePartition := cubeRotationMeasure.prod volume
instance cubePartition_probability : IsProbabilityMeasure cubePartitionMeasure := by
  unfold cubePartitionMeasure
  infer_instance

lemma physicalGridPressure_partition_integrable (b : ℝ) (x : Configuration N) :
    Integrable (fun p : CubePartition => physicalGridPressure b p.1 p.2 x) cubePartitionMeasure := by
  have hh := bounded_average_section_integrable (μ := cubePartitionMeasure)
    (P := fun (p : CubePartition) (y : Configuration N) => physicalGridPressure b p.1 p.2 y)
    (physicalGridPressure_measurable (N := N) b)
    (fun p y => physicalGridPressure_nonneg b p.1 p.2 y)
    (fun p y => physicalGridPressure_le b p.1 p.2 y) x
  exact hh

lemma physicalPressureAverage_partition (b : ℝ) (x : Configuration N) :
    physicalPressureAverage b x = ∫ p : CubePartition, physicalGridPressure b p.1 p.2 x ∂cubePartitionMeasure := by
  rw [cubePartitionMeasure,integral_prod _ (physicalGridPressure_partition_integrable b x)]
  unfold physicalGridPressure
  simp only [integral_const_mul]
  rfl

lemma physicalPressureAverage_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (b : ℝ) : Integrable (fun x => physicalPressureAverage b x*formDensity ψ x) := by
  apply hψ.formDensity_integrable.bdd_mul (physicalPressureAverage_measurable b).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (physicalPressureAverage_nonneg _ _)]
    exact physicalPressureAverage_le _ _

lemma physicalPressure_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) : Integrable (fun x => physicalPressure b x*formDensity ψ x) := by
  apply hψ.formDensity_integrable.bdd_mul (physicalPressure_measurable b).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (physicalPressure_nonneg hb x)]
    exact (physicalPressure_le_average hb x).trans (physicalPressureAverage_le b x)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

theorem SobolevFermion.neumann_averaged_pressure {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) :
    tfKinetic*(∫ x, physicalPressureAverage b x*formDensity ψ x) ≤ formKinetic ψ+
      b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  simp_rw [physicalPressureAverage_partition]
  exact weighted_average_bound (μ := cubePartitionMeasure)
    (P := fun (p : CubePartition) (y : Configuration N) => physicalGridPressure b p.1 p.2 y)
    (physicalGridPressure_measurable (N := N) b)
    (fun p x => physicalGridPressure_nonneg b p.1 p.2 x)
    (fun p x => physicalGridPressure_le b p.1 p.2 x)
    hψ.formDensity_integrable (fun p => hψ.neumann_physical_grid hb p.1 p.2)

theorem SobolevFermion.neumann_radial_smear {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) :
    tfKinetic*(∫ x, physicalPressure b x*formDensity ψ x) ≤ formKinetic ψ+
      b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  apply le_trans _ (hψ.neumann_averaged_pressure hb)
  apply mul_le_mul_of_nonneg_left _ (by unfold tfKinetic; positivity)
  exact integral_mono (physicalPressure_value_integrable hψ hb) (physicalPressureAverage_value_integrable hψ b)
    (fun x => mul_le_mul_of_nonneg_right (physicalPressure_le_average hb x) (formDensity_nonneg ψ x))

theorem FormAdmissible.neumann_radial_smear {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {b : ℝ} (hb : 0 < b) :
    tfKinetic*(∫ x, physicalPressure b x*formDensity ψ x) ≤ formKinetic ψ+
      b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ)) := by
  have hh := hψ.sobolevFermion.neumann_radial_smear hb
  unfold formMass at hh
  simpa only [hψ.2.2.2.2.1,mul_one] using hh

end CoulombAtom

end

end OAI
