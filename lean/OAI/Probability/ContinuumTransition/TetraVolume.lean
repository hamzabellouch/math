import OAI.Probability.ContinuumTransition.Tetrahedron

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

def tetraTrial (t r : ℝ) (c : Space) : Set (Fin 4 → Space) :=
  {x | x 0 ∈ Metric.closedBall c (r/2) ∧ ∀ j : Fin 3,
    x j.succ ∈ Metric.closedBall (x 0+Real.exp (-t) • tetraVertex j.succ) (clusterRadius t)}

lemma measurableSet_tetraTrial (t r : ℝ) (c : Space) : MeasurableSet (tetraTrial t r c) := by
  apply ((measurableSet_closedBall).preimage (measurable_pi_apply 0)).inter
  apply measurableSet_forall_labels
  intro j
  change MeasurableSet {x : Fin 4 → Space | ‖x j.succ-(x 0+Real.exp (-t) • tetraVertex j.succ)‖ ≤ clusterRadius t}
  exact measurableSet_le
    (((measurable_pi_apply j.succ : Measurable (fun x : Fin 4 → Space => x j.succ)).sub
      ((measurable_pi_apply 0).add measurable_const)).norm) measurable_const

lemma tetraTrial_cluster {t r : ℝ} {c : Space} {x : Fin 4 → Space}
    (hx : x ∈ tetraTrial t r c) : TetraCluster t x := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [sub_self,tetraVertex_zero,smul_zero,norm_zero]
    exact (clusterRadius_pos t).le
  · have hh := hx.2 j
    rw [Metric.mem_closedBall,dist_eq_norm] at hh
    have he : (x j.succ-x 0)-Real.exp (-t) • tetraVertex j.succ =
        x j.succ-(x 0+Real.exp (-t) • tetraVertex j.succ) := by module
    rw [he]
    exact hh

lemma tetraTrial_subset {t r : ℝ} {c : Space} (ht : 2*Real.exp (-t) ≤ r/2) :
    tetraTrial t r c ⊆ {x | ∀ i, x i ∈ Metric.closedBall c r} := by
  intro x hx i
  rw [Metric.mem_closedBall,dist_eq_norm]
  have hi := tetraCluster_norm_le (tetraTrial_cluster hx) i
  have h0 := hx.1
  rw [Metric.mem_closedBall,dist_eq_norm] at h0
  have hh := norm_sub_le_norm_sub_add_norm_sub (x i) (x 0) c
  linarith

lemma volume_tetraTrial (t r : ℝ) (c : Space) :
    volume (tetraTrial t r c) = volume (Metric.closedBall c (r/2))*
      (volume (Metric.closedBall (0 : Space) (clusterRadius t)))^3 := by
  let T : Set (Space × (Fin 3 → Space)) := {z | z.1 ∈ Metric.closedBall c (r/2) ∧
    ∀ j, z.2 j ∈ Metric.closedBall (z.1+Real.exp (-t) • tetraVertex j.succ) (clusterRadius t)}
  have hm : MeasurableSet T := by
    apply (measurableSet_closedBall.preimage measurable_fst).inter
    apply measurableSet_forall_labels
    intro j
    change MeasurableSet {z : Space × (Fin 3 → Space) |
      ‖z.2 j-(z.1+Real.exp (-t) • tetraVertex j.succ)‖ ≤ clusterRadius t}
    exact measurableSet_le
      ((((measurable_pi_apply j : Measurable (fun x : Fin 3 → Space => x j)).comp measurable_snd).sub
        (measurable_fst.add measurable_const)).norm) measurable_const
  have hp := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => Space) 0
  have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => Space) 0) ⁻¹' T =
      tetraTrial t r c := by
    ext x
    rfl
  have he := hp.measure_preimage hm.nullMeasurableSet
  rw [hpre] at he
  rw [he]
  change (volume.prod volume) T = _
  rw [Measure.prod_apply hm]
  have hf (a : Space) : volume (Prod.mk a ⁻¹' T) =
      (Metric.closedBall c (r/2)).indicator
        (fun _ => (volume (Metric.closedBall (0 : Space) (clusterRadius t)))^3) a := by
    by_cases ha : a ∈ Metric.closedBall c (r/2)
    · rw [indicator_of_mem ha]
      have he : Prod.mk a ⁻¹' T = Set.pi Set.univ
          (fun j : Fin 3 => Metric.closedBall (a+Real.exp (-t) • tetraVertex j.succ) (clusterRadius t)) := by
        ext b
        simp only [T, mem_preimage, mem_ofPred_eq, ha, true_and, mem_pi, mem_univ, forall_true_left]
      rw [he, volume_pi, Measure.pi_pi]
      simp only [Measure.addHaar_closedBall_center, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · rw [indicator_of_notMem ha]
      have he : Prod.mk a ⁻¹' T = ∅ := by
        ext b
        simp only [T, mem_preimage, mem_ofPred_eq, mem_empty_iff_false]
        exact iff_false_intro (fun hh => ha hh.1)
      rw [he,measure_empty]
  simp_rw [hf]
  rw [lintegral_indicator_const measurableSet_closedBall]
  exact mul_comm _ _

lemma freeConfig_core_energy {ι : Type} [Fintype ι] {t : ℝ} (ht : 1 < t)
    {x : ι → Space} (hx : FreeConfig t x) :
    gibbsEnergy (fun x y => coreProfile t ‖x-y‖) x = 0 := by
  unfold gibbsEnergy
  have he (i j : ι) : (if i=j then 0 else coreProfile t ‖x i-x j‖) = 0 := by
    split_ifs with hij
    · rfl
    · by_cases hd : ‖x i-x j‖ < 1
      · obtain ⟨hlo,hup⟩ := hx i j hij hd
        simp only [coreProfile, ite_eq_right (not_lt_of_ge hlo), ite_eq_left hup]
      · exact coreProfile_eq_zero ht (le_of_not_gt hd)
  simp_rw [he]
  simp

lemma tetraTrial_gibbs {t r β d : ℝ} (ht : 1 < t) {c : Space} {x : Fin 4 → Space}
    (hx : x ∈ tetraTrial t r c) :
    gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d (Fin 4) x = Real.exp (4*d) := by
  have hf := tetraCluster_free (tetraTrial_cluster hx)
  simp only [gibbsFamily,ite_eq_left (freeConfig_injective hf),freeConfig_core_energy ht hf,
    Fintype.card_fin,Nat.cast_ofNat,mul_zero,sub_zero,mul_comm d]

lemma tetraTrial_term_lower {t β r : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hr : 2*Real.exp (-t) ≤ r/2) (d : ℝ) (c : Space) :
    volume.real (Metric.closedBall c (r/2))*(volume.real (Metric.closedBall (0 : Space) (clusterRadius t)))^3*
      Real.exp (4*d)/24 ≤ familyTerm (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d)
        (Metric.closedBall c r) 4 := by
  have hi := (core_gibbs_finite t d hβ (measure_closedBall_lt_top.ne) (D := Metric.closedBall c r)).integrable (Fin 4)
  have hs := tetraTrial_subset (c := c) hr
  have he : (∫ x in tetraTrial t r c, gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d (Fin 4) x) =
      volume.real (tetraTrial t r c)*Real.exp (4*d) := by
    rw [setIntegral_congr_fun (measurableSet_tetraTrial t r c) (fun x hx => tetraTrial_gibbs ht hx),
      setIntegral_const,smul_eq_mul]
  have hh := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (gibbsFamily_nonneg (fun x y => coreProfile t ‖x-y‖) β d (Fin 4)))
    (Filter.Eventually.of_forall hs)
  change (∫ x in tetraTrial t r c, gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d (Fin 4) x) ≤ _ at hh
  rw [he,Measure.real,volume_tetraTrial,ENNReal.toReal_mul,ENNReal.toReal_pow] at hh
  have hd := div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ 24 by norm_num)
  simpa [familyTerm, familyIntegral, Nat.factorial, Measure.real] using hd

end ContinuumTemperature
end

end OAI
