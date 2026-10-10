import OAI.Probability.SLE.Stochastic.PlanarWienerIncrements

namespace OAI

/-! Full-past filtration and restricted Gaussian increment laws for the
actual two-coordinate Wiener path. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

def planarWienerFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Driver×Driver)) :=
  Filtration.natural planarWiener (fun t => (measurable_planarWiener t).stronglyMeasurable)

lemma planarWienerFiltration_le_past (s : ℝ≥0) :
    planarWienerFiltration s ≤ MeasurableSpace.comap (planarWienerPast s) inferInstance := by
  rw [planarWienerFiltration,Filtration.natural_eq_comap]
  have hp : Measurable[MeasurableSpace.comap (planarWienerPast s) inferInstance]
      (planarWienerPast s) := measurable_iff_comap_le.mpr le_rfl
  have hm : Measurable[MeasurableSpace.comap (planarWienerPast s) inferInstance]
      (fun b : Driver×Driver => fun t : Iic s => planarWiener t b) := by
    let : MeasurableSpace (Driver×Driver) :=
      MeasurableSpace.comap (planarWienerPast s) inferInstance
    apply measurable_pi_iff.mpr
    intro t
    exact ((measurable_pi_apply t).comp (measurable_fst.comp hp)).prodMk
      ((measurable_pi_apply t).comp (measurable_snd.comp hp))
  exact hm.comap_le

lemma planarWiener_increment_indep_filtration
    (W : WienerLaw) (hW : IsWiener W) (s δ : ℝ≥0) :
    Indep (planarWienerFiltration s)
      (MeasurableSpace.comap (fun b => planarWiener (s+δ) b-planarWiener s b) inferInstance)
      (W.prod W) := by
  have hi := (IndepFun_iff_Indep _ _ _).mp (planarWiener_increment_indep_past W hW s δ)
  exact indep_of_indep_of_le hi (planarWienerFiltration_le_past s) le_rfl

lemma planarWiener_increment_restrict_law
    (W : WienerLaw) (hW : IsWiener W) (s δ : ℝ≥0)
    (A : Set (Driver×Driver)) (hA : MeasurableSet[planarWienerFiltration s] A) :
    ((W.prod W).restrict A).map (fun b => planarWiener (s+δ) b-planarWiener s b) =
      (W.prod W) A • (gaussianReal 0 δ).prod (gaussianReal 0 δ) := by
  have hm : Measurable (fun b => planarWiener (s+δ) b-planarWiener s b) :=
    (measurable_planarWiener (s+δ)).sub (measurable_planarWiener s)
  have hi := planarWiener_increment_indep_filtration W hW s δ
  have hL := planarWiener_increment_law W hW s δ
  ext S hS
  rw [Measure.map_apply hm hS,Measure.restrict_apply (hm hS),Measure.smul_apply,smul_eq_mul]
  rw [inter_comm]
  rw [(hi.indepSet_of_measurableSet hA ⟨S,hS,rfl⟩).measure_inter_eq_mul]
  exact congrArg (fun x => (W.prod W) A*x) (hL.measure_eq hS)

end SLEExactGauge

end

end OAI
