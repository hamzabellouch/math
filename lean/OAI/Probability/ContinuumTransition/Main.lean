import OAI.Probability.ContinuumTransition.ConstructionLimit

namespace OAI

section
open scoped Topology BigOperators
open Set Filter Metric MeasureTheory
noncomputable section
namespace ContinuumTemperature

lemma SlopeBall_subset_closedBall {g : Parameter} {γ : ℝ} (hγ : 0 ≤ γ) :
    SlopeBall g γ ⊆ closedBall g γ := by
  intro v hv
  change (v.1-g.1)^2+(v.2-g.2)^2 ≤ γ^2 at hv
  simp only [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
    Real.norm_eq_abs,max_le_iff]
  constructor
  · nlinarith only [hv,sq_nonneg (v.2-g.2),sq_abs (v.1-g.1),abs_nonneg (v.1-g.1),hγ]
  · nlinarith only [hv,sq_nonneg (v.1-g.1),sq_abs (v.2-g.2),abs_nonneg (v.2-g.2),hγ]

theorem main_theorem : MainStatement := by
  obtain ⟨C⟩ := exists_constructionData
  obtain ⟨x,hx,hnear⟩ := C.exists_limit_position
  have ht : 1 < C.t := C.cap.t_large
  have ht0 : 0 < C.t := lt_trans zero_lt_one ht
  have hsmall : 2197*C.t*kernelHeight*(∑' k, C.masses k)/2 ≤ C.t^2/8 := by
    have hh := C.cap.small C.mass_bound
    nlinarith only [hh,sq_nonneg C.t]
  have hφ : Measurable (radialPotential C.profile) :=
    measurable_radialPotential (measurable_physicalProfile C.t C.masses_nonneg C.ranges_one C.masses_summable)
  have hstable := physicalProfile_stable ht0.le C.masses_nonneg C.ranges_one C.masses_summable hsmall
  have hcore : ∀ r, 0 < r → C.profile r ≤ coreProfile C.t r :=
    fun r _ => physicalProfile_le_core ht0.le C.masses_nonneg C.ranges_one r
  have hβ : 0 < x.1 := moderateBox_subset (initial_near_moderate hnear)
  have hball : ∀ v ∈ SlopeBall (triangleCenter packingDensity) C.γ, Supports C.pressure x v := by
    intro v hv
    apply supports_iff_supportOn.mpr
    exact C.limit_support_ball packingDensity_pos hx hnear (SlopeBall_subset_closedBall C.γ_pos.le hv)
  have hg : 0 < (triangleCenter packingDensity).2 := by
    change 0 < 5*packingDensity/3
    positivity [packingDensity_pos]
  obtain ⟨I,hIo,hIc,hIn,hIp,hjump⟩ := canonical_interval_of_support_ball
    (physical_partialConjugate hφ ht hstable hcore) ht0 hβ C.γ_pos hg
    (fun d hd => concaveOn_physicalCanonical hφ ht hstable hcore hd.le) hball
  refine ⟨C.profile,canonicalFreeEnergy C.profile,I,x.1,?_,?_,?_,hIo,hIc,hIn,hIp,initial_near_beta hnear,?_⟩
  · exact admissible_physicalProfile ht C.masses_nonneg C.ranges_one C.masses_summable hsmall
      (C.stages 0).a_pos (C.transitions 0).range_large.le
  · exact physicalProfile_isLittleO ht C.masses_nonneg C.ranges_one C.masses_summable
  · exact hasCanonicalFreeEnergy_of_core hφ ht hstable hcore
  · intro d hd
    obtain ⟨l,r,hl,hr,_,hstrict⟩ := hjump d hd
    have he : (fun β => C.t*physicalCanonical C.profile C.t β d/β) =
        fun β => canonicalFreeEnergy C.profile β d := by
      funext β
      simp only [physicalCanonical,canonicalFreeEnergy]
      congr 1
      field_simp
    rw [he] at hl hr
    exact ⟨l,r,hl,hr,hstrict⟩

end ContinuumTemperature
end
end

end OAI
