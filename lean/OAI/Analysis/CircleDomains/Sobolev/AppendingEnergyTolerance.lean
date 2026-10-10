import OAI.Analysis.CircleDomains.Selection.AppendingPairData
import OAI.Analysis.CircleDomains.Sobolev.SavedBarrierEnergySlack

namespace OAI

/-! A finite saved family has a common positive energy tolerance. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_common_positive_fin {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ t > 0, ∀ i, t ≤ r i := by
  induction n with
  | zero => exact ⟨1,zero_lt_one,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨t,ht,hti⟩ := ih (fun i => r i.succ) (fun i => hr i.succ)
    refine ⟨min (r 0) t,lt_min (hr 0) ht,?_⟩
    intro i
    exact Fin.cases (min_le_left _ _) (fun j => (min_le_right _ _).trans (hti j)) i

 theorem AppendingPairData.exists_energy_tolerance
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {a δ η : ℝ} (D : AppendingPairData G u Wold a δ η)
    (hG : IsOpen G) {n : ℕ} (c : Fin n → EuclideanPlane) :
    ∃ t > 0, ∀ i (p q : EuclideanPlane → ℝ), Continuous p → Continuous q →
      ∀ (Wp : DeGiorgi.MemW1pWitness 2 p (physicalPlaneDomain G ∩ ball 0 (65*a)))
        (Wq : DeGiorgi.MemW1pWitness 2 q (physicalPlaneDomain G ∩ ball 0 (65*a))),
      (∀ z ∈ physicalPlaneDomain G ∩ ball 0 (65*a),
        ‖planePair (p z) (q z)-planePair (D.p z) (D.q z)‖ ≤ t) →
      (eLpNorm (fun z => Wp.weakGrad z-D.p_witness.weakGrad z) 2
        (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal ≤ t →
      (eLpNorm (fun z => Wq.weakGrad z-D.q_witness.weakGrad z) 2
        (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal ≤ t →
      ∃ W : DeGiorgi.MemW1pWitness 2 (fun z => D.barrier (planePair (p z) (q z)-c i))
        (physicalPlaneDomain G ∩ ball 0 (65*a)),
        (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η := by
  classical
  let U := physicalPlaneDomain G ∩ ball (0 : EuclideanPlane) (65*a)
  have hU : IsOpen U := (isOpen_physicalPlaneDomain hG).inter isOpen_ball
  have hUf : volume U ≠ (⊤ : ℝ≥0∞) :=
    ((measure_mono (inter_subset_right : U ⊆ ball 0 (65*a))).trans_lt measure_ball_lt_top).ne
  let Wx := D.p_witness.restrict hU inter_subset_left
  let Wy := D.q_witness.restrict hU inter_subset_left
  obtain ⟨C,hC⟩ := (D.barrier_compact.fderiv ℝ).exists_bound_of_continuous
    (D.barrier_smooth.continuous_fderiv (by simp))
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (D.barrier_compact.fderiv ℝ)
    (D.barrier_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)) (by simp)
  have hDD : ∀ x y, ‖fderiv ℝ D.barrier x-fderiv ℝ D.barrier y‖ ≤ (K : ℝ)*‖x-y‖ :=
    fun x y => by simpa only [dist_eq_norm] using hK.dist_le_mul x y
  have hdata (i : Fin n) : ∃ t > 0, ∀ (p q : EuclideanPlane → ℝ), Continuous p → Continuous q →
      ∀ (Wp : DeGiorgi.MemW1pWitness 2 p U) (Wq : DeGiorgi.MemW1pWitness 2 q U),
      (∀ z ∈ U, ‖planePair (p z) (q z)-planePair (D.p z) (D.q z)‖ ≤ t) →
      (eLpNorm (fun z => Wp.weakGrad z-Wx.weakGrad z) 2 (volume.restrict U)).toReal ≤ t →
      (eLpNorm (fun z => Wq.weakGrad z-Wy.weakGrad z) 2 (volume.restrict U)).toReal ≤ t →
      ∃ W : DeGiorgi.MemW1pWitness 2 (fun z => D.barrier (planePair (p z) (q z)-c i)) U,
        (eLpNorm W.weakGrad 2 (volume.restrict U)).toReal < η := by
    obtain ⟨V,hV⟩ := D.small_energy (c i)
    obtain ⟨hΦ,_,_,hunit,_,hD,hDD'⟩ := translatedPhysicalBarrier_data D.barrier_smooth
      D.barrier_compact D.barrier_support D.barrier_unit D.barrier_one
      (fun x => (hC x).trans (le_max_left C 0)) hDD (c i)
    exact exists_saved_barrier_energy_tolerance hU hUf D.p_continuous D.q_continuous Wx Wy
      (hΦ.of_le (by simp)) (show (0 : ℝ) ≤ 1 by norm_num) (le_max_right C 0) K.coe_nonneg
      (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hunit x).1]; exact (hunit x).2)
      hD hDD' V hV
  choose r hr hri using hdata
  obtain ⟨t,ht,htr⟩ := exists_common_positive_fin r hr
  refine ⟨t,ht,?_⟩
  intro i p q hp hq Wp Wq hclose hpE hqE
  exact hri i p q hp hq Wp Wq (fun z hz => (hclose z hz).trans (htr i))
    (hpE.trans (htr i)) (hqE.trans (htr i))

end CircleDomainRigidity

end

end OAI
