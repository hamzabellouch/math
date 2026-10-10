import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicy

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma annealed_crossing_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    (∫⁻ ω, crossingQuenched ℓ x H ω ∂environmentLaw ν)=annealedLaw ν (Cross ℓ 0 H) := by
  simp_rw [crossingQuenched_translation ℓ x]
  rw [← lintegral_map (measurable_crossingQuenched ℓ 0 H) (by fun_prop),environment_translation,
    annealed_apply ν (measurableSet_cross ℓ 0 H)]
  rfl

lemma annealed_record_cylinder_cross {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Path d) (n : ℕ) (hn : 0<n) (hr : StrictRecord ℓ f n)
    (H : ℝ) (hH : 0<H) :
    annealedLaw ν ((fun X : Path d => fun j => X (n+j)) ⁻¹' Cross ℓ (f n) H ∩ pathCylinder f n)=
      annealedLaw ν (pathCylinder f n)*annealedLaw ν (Cross ℓ 0 H) := by
  by_cases hf : f 0=0
  · let S : Set (Lattice d) := {y | ∃ j<n, y=f j}
    let T := Strip ℓ (f n) H
    have hST : Disjoint S T := by
      apply Set.disjoint_left.mpr
      rintro y ⟨j,hj,rfl⟩ hy
      exact (not_le_of_gt (hr j hj)) hy.1
    have hS0 : (0 : Lattice d) ∈ S := ⟨0,hn,hf.symm⟩
    have hm : @Measurable _ _ (rowSigma S) _
        (fun ω : Environment d => quenchedKernel (ω,0) (pathCylinder f n)) := by
      apply measurable_of_row_locality _
        ((Kernel.measurable_coe _ (measurableSet_pathCylinder f n)).comp
          (measurable_id.prodMk measurable_const)) S 0 hS0
      intro ω η hωη
      exact pathCylinder_weight_locality S ω η hωη 0 f n (fun j hj => ⟨j,hj,rfl⟩)
    rw [annealed_apply ν ((measurableSet_cross ℓ (f n) H).preimage (by fun_prop) |>.inter
      (measurableSet_pathCylinder f n))]
    simp_rw [quenched_prefix_future _ _ _ hf n (measurableSet_cross ℓ (f n) H)]
    change (∫⁻ ω, quenchedKernel (ω,0) (pathCylinder f n)*crossingQuenched ℓ (f n) H ω
      ∂environmentLaw ν)=_
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hST) hm
      (measurable_crossingQuenched_rows ℓ (f n) hH),annealed_crossing_translation,
      ← annealed_apply ν (measurableSet_pathCylinder f n)]
  · have hzero : annealedLaw ν (pathCylinder f n)=0 := by
      rw [annealed_apply ν (measurableSet_pathCylinder f n)]
      simp_rw [quenched_pathCylinder_zero _ _ _ hf n]
      simp
    rw [measure_mono_null Set.inter_subset_right hzero,hzero,zero_mul]

lemma annealed_record_event_cross {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (n : ℕ) (hn : 0<n) (A : Set (Path d)) (hA : PrefixDetermined n A)
    (hr : ∀ X ∈ A, StrictRecord ℓ X n) (H : ℝ) (hH : 0<H) :
    annealedLaw ν (A ∩ FutureEvent (fun x => Cross ℓ x H) n)=
      annealedLaw ν A*annealedLaw ν (Cross ℓ 0 H) := by
  rw [measure_partition_prefix (annealedLaw ν) (A ∩ _) n,
    measure_partition_prefix (annealedLaw ν) A n,← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro f
  let g := extendPrefix n f
  by_cases hg : g ∈ A
  · have he : (A ∩ FutureEvent (fun x => Cross ℓ x H) n) ∩ pathCylinder g n =
        (fun X : Path d => fun j => X (n+j)) ⁻¹' Cross ℓ (g n) H ∩ pathCylinder g n := by
      ext X
      constructor
      · rintro ⟨⟨_,hc⟩,hX⟩
        exact ⟨by simpa only [FutureEvent,Set.mem_ofPred_eq,Set.mem_preimage,hX n le_rfl] using hc,hX⟩
      · rintro ⟨hc,hX⟩
        exact ⟨⟨(hA X g hX).mpr hg,by simpa only [FutureEvent,Set.mem_ofPred_eq,Set.mem_preimage,hX n le_rfl] using hc⟩,hX⟩
    have hAc : A ∩ pathCylinder g n=pathCylinder g n := by
      rw [prefixDetermined_inter_cylinder A n hA g,ite_eq_left hg]
    rw [he,hAc]
    exact annealed_record_cylinder_cross ν ℓ g n hn (hr g hg) H hH
  · have hzero : A ∩ pathCylinder g n=∅ := by
      rw [prefixDetermined_inter_cylinder A n hA g,ite_eq_right hg]
    have he : (A ∩ FutureEvent (fun x => Cross ℓ x H) n) ∩ pathCylinder g n=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨⟨hXA,_⟩,hX⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hzero) X ⟨hXA,hX⟩
    rw [he,hzero,measure_empty,zero_mul]

end DirectionalTransience

end

end OAI
