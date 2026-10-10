import Mathlib
import OAI.Analysis.HardSphere.Comparison.CellAffinity
import OAI.Analysis.HardSphere.Allocation.AllocatedLinearity

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison

lemma measureAffinity_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X≃ᵐY) (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    measureAffinity (P.map e) (Q.map e)=measureAffinity P Q := by
  unfold measureAffinity affinity
  rw [←Measure.map_add _ _ e.measurable,e.measurableEmbedding.integral_map]
  apply integral_congr_ae
  filter_upwards [e.measurableEmbedding.rnDeriv_map P (P+Q),e.measurableEmbedding.rnDeriv_map Q (P+Q)] with x hx hy
  rw [hx,hy]

lemma actual_common_gain {X : Type*} [MeasurableSpace X] (σ P Q : Measure X)
    [IsFiniteMeasure σ] [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {B : ℝ} (hB : 1 ≤ B) (hm : (1/2:ℝ≥0∞) ≤ σ univ)
    (hp : σ≪P) (hq : σ≪Q)
    (hip : Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P)
    (hiq : Integrable (fun z ↦ (σ.rnDeriv Q z).toReal^2) Q)
    (hmp : (∫z,(σ.rnDeriv P z).toReal^2 ∂P) ≤ 2*B)
    (hmq : (∫z,(σ.rnDeriv Q z).toReal^2 ∂Q) ≤ 2*B) :
    1/(8*B) ≤ measureAffinity P Q := by
  have hm' : (1/2:ℝ) ≤ σ.real univ := by
    have H := ENNReal.toReal_mono (measure_ne_top σ univ) hm
    norm_num [Measure.real] at H ⊢
    exact H
  have h := common_measure_affinity hp hq (by linarith : 0 < σ.real univ) hip hiq hmp hmq
  rw [show (2*B)*(2*B)=(2*B)^2 by ring,Real.sqrt_sq (by linarith : 0 ≤ 2*B)] at h
  refine le_trans ?_ h
  apply (div_le_div_iff₀ (by linarith : 0 < 8*B) (by linarith : 0 < 2*B)).mpr
  have hm2 : (1/4:ℝ) ≤ (σ.real univ)^2 := by nlinarith
  nlinarith

end HardSphere.Comparison

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

lemma physical_cell_posts_sum {N K : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1 ≤ K) (b : Bool)
    (P : Measure (Torus L×Configuration N L)) [SFinite P] :
    (∑tag : Fin 3→Fin K,∑extra : Fin 3→Fin K,
      physicalCellVolumePost L extra tag b ∘ₘ P)=
      (P.prod volume).map (cellObservation b) := by
  simp_rw [physicalCellVolumePost,←Measure.map_comp _ _ (cellObservation_measurable b),
    cellExtraKernel_comp _ volume _ _ (centeredCell_measurable L _) (centeredCell_measurable L _)]
  simp_rw [←Measure.map_finset_sum' (cellObservation_measurable b).aemeasurable]
  congr 1
  have he (tag extra : Fin 3→Fin K) :
      {p : (Torus L×Configuration N L)×Torus L |
        p.1.1∈centeredCell L (gridCenter L tag) ∧ p.2∈centeredCell L (gridCenter L extra)}=
      {p | (gridHome hL p.1.1,gridHome hL p.2)=(tag,extra)} := by
    ext p
    simp only [Set.mem_ofPred_eq,Prod.mk.injEq,gridHome_eq_iff hL hK]
  simp_rw [he]
  rw [←Fintype.sum_prod_type (fun ij : (Fin 3→Fin K)×(Fin 3→Fin K) ↦
    (P.prod volume).restrict {p | (gridHome hL p.1.1,gridHome hL p.2)=ij})]
  apply sum_restrict_partition
  intro i
  exact (((gridHome_measurable hL).comp (measurable_fst.comp measurable_fst)).prodMk
    ((gridHome_measurable hL).comp measurable_snd)) (measurableSet_singleton i)

end HardSphere.Groups
end
end

end OAI
