import Mathlib
import OAI.Analysis.Conductivity.Branching.ParentFullEndEnergy
import OAI.Analysis.Conductivity.Walls.ChildSeamCutoff

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem centralChild_complement_partition (k : Fin 2) :
    ∃ (l : ℝ) (η : (Fin 3 → ℝ) → ℝ),-centralThickness<l ∧ l<0 ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) η ∧ HasCompactSupport η ∧
      (∀ y,|η y|≤1) ∧ tsupport η⊆sourceClosedCollarBand l (centralThickness/2) ∧
      (∀ y,sourceCollarTime y≤-centralThickness → η=ᶠ[𝓝 y] 0) ∧
      (∀ y∈sourceClosedCollarBand (-centralThickness) 0,
        (fun z => centralJoinChildCutoff k z+η z)=ᶠ[𝓝 y] (fun _ => 1)) := by
  let χ : (Fin 3 → ℝ) → ℝ := centralJoinChildCutoff k
  let q := fun y => 1-χ y
  let K := sourceClosedCollarBand (-centralThickness) 0 ∩ tsupport q
  have hK : IsCompact K :=
    (isCompact_sourceClosedCollarBand (show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness])
      (show (0:ℝ)≤1/100 by norm_num)).inter_right (isClosed_tsupport q)
  have hKt (y) (hy : y∈K) : -centralThickness<sourceCollarTime y := by
    apply lt_of_le_of_ne hy.1.1
    intro he
    have hn : y∉tsupport q := notMem_tsupport_iff_eventuallyEq.mpr (by
      filter_upwards [centralJoinChildCutoff_one k he.symm] with z hz
      change 1-χ z=0
      change χ z=1 at hz
      rw [hz]; ring)
    exact hn hy.2
  have hl : ∃ l : ℝ,-centralThickness<l ∧ l<0 ∧ ∀ y∈K,l<sourceCollarTime y := by
    by_cases hn : K.Nonempty
    · obtain ⟨y,hy,hmin⟩ := hK.exists_isMinOn hn locallyLipschitz_sourceCollarTime.continuous.continuousOn
      refine ⟨(sourceCollarTime y-centralThickness)/2,?_,?_,?_⟩
      · linarith [hKt y hy]
      · have hp := hy.1.2
        have : (0:ℝ)<centralThickness := by norm_num [centralThickness]
        linarith
      · intro z hz
        have hh : sourceCollarTime y ≤ sourceCollarTime z := hmin hz
        linarith [hKt y hy]
    · refine ⟨-centralThickness/2,by norm_num [centralThickness],by norm_num [centralThickness],?_⟩
      intro y hy
      exact (hn ⟨y,hy⟩).elim
  obtain ⟨l,hl,hl₀,hlK⟩ := hl
  have hl' : -(1:ℝ)/100≤l := (show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans hl.le
  have hbig := isCompact_sourceClosedCollarBand hl'
    (show centralThickness/2≤1/100 by norm_num [centralThickness])
  have hi : K⊆interior (sourceClosedCollarBand l (centralThickness/2)) := by
    intro y hy
    apply mem_interior_iff_mem_nhds.mpr
    have hm := locallyLipschitz_sourceCollarTime.continuous.continuousAt
      (isOpen_Ioo.mem_nhds (show sourceCollarTime y∈Ioo l (centralThickness/2) from
        ⟨hlK y hy,by have := hy.1.2; dsimp [centralThickness] at *; linarith⟩))
    exact mem_of_superset hm (fun z hz => ⟨hz.1.le,hz.2.le⟩)
  obtain ⟨ψ,hψ1,hψ0,hψb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) hK.isClosed hi (n:=↑(⊤:ℕ∞))
  have hψc : HasCompactSupport ψ := HasCompactSupport.intro hbig hψ0
  have hψs : tsupport ψ⊆sourceClosedCollarBand l (centralThickness/2) := by
    apply closure_minimal _ hbig.isClosed
    intro y hy
    by_contra hn
    exact hy (hψ0 y hn)
  let η := fun y => q y*ψ y
  have hηs : tsupport η⊆sourceClosedCollarBand l (centralThickness/2) :=
    tsupport_mul_subset_right.trans hψs
  refine ⟨l,η,hl,hl₀,(contDiff_const.sub (centralJoinChildCutoff_smooth k)).mul ψ.contMDiff.contDiff,
    hψc.mul_left,?_,hηs,?_,?_⟩
  · intro y
    have h₀ := centralJoinPartition.nonneg (centralChildPatch k) (sourceChildCoordinates (actualChildSign k) y)
    have h₁ := centralJoinPartition.le_one (centralChildPatch k) (sourceChildCoordinates (actualChildSign k) y)
    change 0≤χ y at h₀
    change χ y≤1 at h₁
    have h₂ := (hψb y).1
    have h₃ := (hψb y).2
    dsimp only [η,q]
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr h₁) h₂)]
    nlinarith [mul_nonneg h₀ h₂]
  · intro y hy
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hn
    have hle := (hηs hn).1
    linarith
  · intro y hy
    by_cases hk : y∈K
    · have hψ := hψ1.filter_mono (nhds_le_nhdsSet hk)
      filter_upwards [hψ] with z hz
      change centralJoinChildCutoff k z+((1-centralJoinChildCutoff k z)*ψ z)=1
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

theorem childAttachedCorrection_exists (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure,sourceCollarTime (WithLp.ofLp x)≤-centralThickness →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand (-centralThickness) 0 →
        weakValue (childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
          (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
          (centralJoinChildCutoff_support k) p+d) x=
          fullAttachedEndValue s (centralT s k.succ p) a (-centralThickness) κ (WithLp.ofLp x) ∧
        ∀ i,weakGradient (childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
          (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
          (centralJoinChildCutoff_support k) p+d) x i=
          fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ (WithLp.ofLp x) i) := by
  obtain ⟨l,η,hl,hl₀,hη,hηc,hηb,hηs,hηzero,hpart⟩ := centralChild_complement_partition k
  obtain ⟨v,hv,hve⟩ := compact_collar_slope_value_gradient (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k) ha.ne'
    (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    κ (-2*centralThickness) 0 (by norm_num [centralThickness]) (by norm_num) (centralJoinChildCutoff_support k)
  have hR : 0≤a*(3*centralThickness/2) :=
    mul_nonneg ha.le (by norm_num [centralThickness])
  have hT : ∀ t∈Icc l (centralThickness/2),
      affineEndTime a (-centralThickness) t∈Icc 0 (a*(3*centralThickness/2)) := by
    intro t ht
    dsimp only [affineEndTime]
    constructor
    · exact mul_nonneg ha.le (sub_nonneg.mpr (hl.le.trans ht.1))
    · have hm := mul_nonneg ha.le (sub_nonneg.mpr ht.2)
      nlinarith
  have hpos : ∀ t∈Icc l (centralThickness/2),0<a*(t-(-centralThickness)) :=
    fun t ht => mul_pos ha (sub_pos.mpr (hl.trans_le ht.1))
  obtain ⟨z,hz,hze⟩ := cut_fullAttachedEnd_H10 s hs (centralT s k.succ p) κ ha.ne' hR
    (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    (show l≤centralThickness/2 by
      have ht : (0:ℝ)<centralThickness := by norm_num [centralThickness]
      linarith)
    ((show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans hl.le)
    (by norm_num [centralThickness])
    hT hpos hη hηc hηb hηs
  refine ⟨v+z,H10.add_mem hv hz,?_,?_⟩
  · filter_upwards [hve,hze,weakValue_add v z,weakGradient_add v z] with x hx hy hval hgrad hcentral
    have hn : a*(sourceCollarTime (WithLp.ofLp x)-(-centralThickness))≤0 :=
      mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hcentral)
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
        ite_eq_right (not_lt_of_ge hn),he,hd,_root_.zero_apply,mul_zero,zero_mul,add_zero]
  · have hne := ae_restrict_of_ae (s:=ball)
      ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
        (sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
          norm_num [centralThickness])))
    have hp : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand (-centralThickness) 0 →
        0<a*(sourceCollarTime (WithLp.ofLp x)-(-centralThickness)) := by
      filter_upwards [hne] with x hx hb
      exact mul_pos ha (sub_pos.mpr (lt_of_le_of_ne hb.1 (Ne.symm hx)))
    have hh := fullEnd_partition_jet s (centralT s k.succ p) a (-centralThickness) κ
      (centralJoinChildCutoff_smooth k) hη hpart (v:=v) (z:=z)
      (u:=childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
        (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
        (centralJoinChildCutoff_support k) p) hp
      (childCompletionJoin_end_ae s hs ha k (centralJoinChildCutoff_smooth k)
        (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
        (centralJoinChildCutoff_support k) p) hve hze
    simpa only [add_assoc] using hh

end ScalarConductivity

end

end OAI
