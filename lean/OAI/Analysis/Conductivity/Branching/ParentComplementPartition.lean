import Mathlib
import OAI.Analysis.Conductivity.Branching.ParentCompletedEndJet
import OAI.Analysis.Conductivity.Variational.EndPartitionJet
import OAI.Analysis.Conductivity.Walls.CentralSeamCutoff

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem centralParent_complement_partition :
    ∃ (r : ℝ) (η : (Fin 3 → ℝ) → ℝ),0<r ∧ r<centralThickness ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) η ∧ HasCompactSupport η ∧
      (∀ y,|η y|≤1) ∧ tsupport η⊆sourceClosedCollarBand (-centralThickness/2) r ∧
      (∀ y∈centralPhysical,η=ᶠ[𝓝 y] 0) ∧
      (∀ y∈sourceClosedCollarBand 0 centralThickness,
        (fun z => centralJoinPartition 1 z+η z)=ᶠ[𝓝 y] (fun _ => 1)) := by
  let χ : (Fin 3 → ℝ) → ℝ := centralJoinPartition 1
  let q := fun y => 1-χ y
  let K := sourceClosedCollarBand 0 centralThickness ∩ tsupport q
  have hK : IsCompact K :=
    (isCompact_sourceClosedCollarBand (show -(1:ℝ)/100≤0 by norm_num)
      (show centralThickness≤1/100 by norm_num [centralThickness])).inter_right (isClosed_tsupport q)
  have hKt (y) (hy : y∈K) : sourceCollarTime y<centralThickness := by
    apply lt_of_le_of_ne hy.1.2
    intro he
    have hn : y∉tsupport q := notMem_tsupport_iff_eventuallyEq.mpr (by
      filter_upwards [centralJoinPartition_parent_one he] with z hz
      change 1-χ z=0
      change χ z=1 at hz
      rw [hz]; ring)
    exact hn hy.2
  have hr : ∃ r : ℝ,0<r ∧ r<centralThickness ∧ ∀ y∈K,sourceCollarTime y<r := by
    by_cases hn : K.Nonempty
    · obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn hn locallyLipschitz_sourceCollarTime.continuous.continuousOn
      refine ⟨(sourceCollarTime y+centralThickness)/2,?_,?_,?_⟩
      · have hp := hy.1.1
        have : (0:ℝ)<centralThickness := by norm_num [centralThickness]
        linarith
      · linarith [hKt y hy]
      · intro z hz
        have hh : sourceCollarTime z ≤ sourceCollarTime y := hmax hz
        linarith [hKt y hy]
    · refine ⟨centralThickness/2,by norm_num [centralThickness],by norm_num [centralThickness],?_⟩
      intro y hy
      exact (hn ⟨y,hy⟩).elim
  obtain ⟨r,hr₀,hr,hrK⟩ := hr
  have hr' : r≤1/100 := hr.le.trans (by norm_num [centralThickness])
  have hbig := isCompact_sourceClosedCollarBand
    (show -(1:ℝ)/100≤-centralThickness/2 by norm_num [centralThickness]) hr'
  have hi : K⊆interior (sourceClosedCollarBand (-centralThickness/2) r) := by
    intro y hy
    apply mem_interior_iff_mem_nhds.mpr
    have hm := locallyLipschitz_sourceCollarTime.continuous.continuousAt
      (isOpen_Ioo.mem_nhds (show sourceCollarTime y∈Ioo (-centralThickness/2) r from
        ⟨by have := hy.1.1; dsimp [centralThickness] at *; linarith,hrK y hy⟩))
    exact mem_of_superset hm (fun z hz => ⟨hz.1.le,hz.2.le⟩)
  obtain ⟨ψ,hψ1,hψ0,hψb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) hK.isClosed hi (n:=↑(⊤:ℕ∞))
  have hψc : HasCompactSupport ψ := HasCompactSupport.intro hbig hψ0
  have hψs : tsupport ψ⊆sourceClosedCollarBand (-centralThickness/2) r := by
    apply closure_minimal _ hbig.isClosed
    intro y hy
    by_contra hn
    exact hy (hψ0 y hn)
  let η := fun y => q y*ψ y
  have hηs : tsupport η⊆sourceClosedCollarBand (-centralThickness/2) r :=
    tsupport_mul_subset_right.trans hψs
  refine ⟨r,η,hr₀,hr,(contDiff_const.sub (centralJoinPartition_smooth 1)).mul ψ.contMDiff.contDiff,
    hψc.mul_left,?_,hηs,?_,?_⟩
  · intro y
    have h₀ := centralJoinPartition.nonneg 1 y
    have h₁ := centralJoinPartition.le_one 1 y
    have h₂ := (hψb y).1
    have h₃ := (hψb y).2
    dsimp only [η,q,χ]
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr h₁) h₂)]
    nlinarith [mul_nonneg h₀ h₂]
  · intro y hy
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hn
    have hle := (hηs hn).2
    have hge := ((centralPhysical_time_iff y).mp hy).1
    linarith
  · intro y hy
    by_cases hk : y∈K
    · have hψ := hψ1.filter_mono (nhds_le_nhdsSet hk)
      filter_upwards [hψ] with z hz
      change centralJoinPartition 1 z+((1-centralJoinPartition 1 z)*ψ z)=1
      rw [hz]
      ring
    · have hq : y∉tsupport q := fun hn => hk ⟨hy,hn⟩
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with z hz
      change q z=0 at hz
      change χ z+q z*ψ z=1
      rw [hz,zero_mul,add_zero]
      dsimp only [q] at hz
      linarith

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem parentAttachedCorrection_exists (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : a<0) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand 0 centralThickness →
        weakValue (parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
          centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
          centralJoinPartition_parent_support p+d) x=
          fullAttachedEndValue s (centralT s 0 p) a centralThickness κ (WithLp.ofLp x) ∧
        ∀ i,weakGradient (parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
          centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
          centralJoinPartition_parent_support p+d) x i=
          fullAttachedEndGradient s (centralT s 0 p) a centralThickness κ (WithLp.ofLp x) i) := by
  obtain ⟨r,η,hr₀,hr,hη,hηc,hηb,hηs,hηzero,hpart⟩ := centralParent_complement_partition
  obtain ⟨v,hv,hve⟩ := compact_collar_slope_value_gradient (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralJoinPartition_bound 1) ha.ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    κ 0 (2*centralThickness) (by norm_num) (by norm_num [centralThickness]) centralJoinPartition_parent_support
  have hR : 0≤-a*(3*centralThickness/2) :=
    mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness])
  have hT : ∀ t∈Icc (-centralThickness/2) r,
      affineEndTime a centralThickness t∈Icc 0 (-a*(3*centralThickness/2)) := by
    intro t ht
    dsimp only [affineEndTime]
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.mpr (ht.2.trans hr.le))
    · have hm := mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr ht.1)
      nlinarith
  have hpos : ∀ t∈Icc (-centralThickness/2) r,0<a*(t-centralThickness) :=
    fun t ht => mul_pos_of_neg_of_neg ha (sub_neg.mpr (ht.2.trans_lt hr))
  obtain ⟨z,hz,hze⟩ := cut_fullAttachedEnd_H10 s hs (centralT s 0 p) κ ha.ne hR
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    (show -centralThickness/2≤r by
      have ht : (0:ℝ)<centralThickness := by norm_num [centralThickness]
      linarith)
    (by norm_num [centralThickness]) (hr.le.trans (by norm_num [centralThickness]))
    hT hpos hη hηc hηb hηs
  refine ⟨v+z,H10.add_mem hv hz,?_,?_⟩
  · filter_upwards [hve,hze,weakValue_add v z,weakGradient_add v z] with x hx hy hval hgrad hcentral
    have ht := ((centralPhysical_time_iff (WithLp.ofLp x)).mp hcentral).1
    have hn : a*(sourceCollarTime (WithLp.ofLp x)-centralThickness)≤0 :=
      mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr ht)
    have he : η (WithLp.ofLp x)=0 := (hηzero _ hcentral).self_of_nhds
    have hd : fderiv ℝ η (WithLp.ofLp x)=0 := by
      rw [(hηzero _ hcentral).fderiv_eq]
      exact fderiv_const_apply (0:ℝ)
    constructor
    · rw [hval]
      simp only [Pi.add_apply,hx.1,hy.1,max_eq_left hn,he,mul_zero,zero_mul,add_zero]
    · intro i
      rw [hgrad]
      simp only [WithLp.ofLp_add,Pi.add_apply,hx.2 i,hy.2 i,max_eq_left hn,
        ite_eq_right (not_lt_of_ge hn),he,hd,zero_apply,mul_zero,zero_mul,add_zero]
  · have hne := ae_restrict_of_ae (s:=ball)
      ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
        (sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
          norm_num [centralThickness])))
    have hp : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand 0 centralThickness →
        0<a*(sourceCollarTime (WithLp.ofLp x)-centralThickness) := by
      filter_upwards [hne] with x hx hb
      exact mul_pos_of_neg_of_neg ha (sub_neg.mpr (lt_of_le_of_ne hb.2 hx))
    have hh := fullEnd_partition_jet s (centralT s 0 p) a centralThickness κ
      (centralJoinPartition_smooth 1) hη hpart (v:=v) (z:=z)
      (u:=parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
        centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
        centralJoinPartition_parent_support p) hp
      (parentCompletionJoin_end_ae s hs ha (centralJoinPartition_smooth 1)
        centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
        centralJoinPartition_parent_support p) hve hze
    simpa only [add_assoc] using hh

end ScalarConductivity

end

end OAI
