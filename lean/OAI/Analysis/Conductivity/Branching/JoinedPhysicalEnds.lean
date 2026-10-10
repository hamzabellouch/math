import Mathlib
import OAI.Analysis.Conductivity.Branching.ParentComplementPartition
import OAI.Analysis.Conductivity.Branching.ChildComplementPartition

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem parentAttachedCorrection_supported (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : a<0) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure, WithLp.ofLp x∉sourceClosedCollarBand (-2*centralThickness) (2*centralThickness) →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,centralThickness ≤ sourceCollarTime (WithLp.ofLp x) →
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
  refine ⟨v+z,H10.add_mem hv hz,?_,?_,?_⟩
  · filter_upwards [hve,hze,weakValue_add v z,weakGradient_add v z] with x hx hy hval hgrad hout
    have hχn : WithLp.ofLp x∉tsupport (centralJoinPartition 1) := by
      intro hm
      apply hout
      have h := centralJoinPartition_parent_support hm
      exact ⟨(by norm_num [centralThickness]; linarith [h.1]),h.2⟩
    have hηn : WithLp.ofLp x∉tsupport η := by
      intro hm
      apply hout
      rcases hηs hm with ⟨hlo,hhi⟩
      constructor <;> dsimp [centralThickness] at * <;> linarith
    have hχ0 := image_eq_zero_of_notMem_tsupport hχn
    have hdχ0 := fderiv_of_notMem_tsupport ℝ hχn
    have hη0 := image_eq_zero_of_notMem_tsupport hηn
    have hdη0 := fderiv_of_notMem_tsupport ℝ hηn
    constructor
    · rw [hval]
      simp [hx.1,hy.1,hχ0,hη0]
    · intro i
      rw [hgrad]
      simp [hx.2 i,hy.2 i,hχ0,hη0,hdχ0,hdη0]

  · filter_upwards [hve,hze,weakValue_add v z,weakGradient_add v z] with x hx hy hval hgrad hcentral
    have ht := hcentral
    have hn : a*(sourceCollarTime (WithLp.ofLp x)-centralThickness)≤0 :=
      mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr ht)
    have hηn : WithLp.ofLp x∉tsupport η := by
      intro hm
      have ht' := (hηs hm).2
      exact (not_le.mpr hr) (ht.trans ht')
    have he : η (WithLp.ofLp x)=0 := image_eq_zero_of_notMem_tsupport hηn
    have hd : fderiv ℝ η (WithLp.ofLp x)=0 := fderiv_of_notMem_tsupport ℝ hηn
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


namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem childAttachedCorrection_supported (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure, WithLp.ofLp x∉sourceClosedCollarBand (-2*centralThickness) (2*centralThickness) →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
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
  refine ⟨v+z,H10.add_mem hv hz,?_,?_,?_⟩
  · filter_upwards [hve,hze,weakValue_add v z,weakGradient_add v z] with x hx hy hval hgrad hout
    have hχn : WithLp.ofLp x∉tsupport (centralJoinChildCutoff k) := by
      intro hm
      apply hout
      have h := centralJoinChildCutoff_support k hm
      exact ⟨h.1,(by norm_num [centralThickness]; linarith [h.2])⟩
    have hηn : WithLp.ofLp x∉tsupport η := by
      intro hm
      apply hout
      rcases hηs hm with ⟨hlo,hhi⟩
      constructor <;> dsimp [centralThickness] at * <;> linarith
    have hχ0 := image_eq_zero_of_notMem_tsupport hχn
    have hdχ0 := fderiv_of_notMem_tsupport ℝ hχn
    have hη0 := image_eq_zero_of_notMem_tsupport hηn
    have hdη0 := fderiv_of_notMem_tsupport ℝ hηn
    constructor
    · rw [hval]
      simp [hx.1,hy.1,hχ0,hη0]
    · intro i
      rw [hgrad]
      simp [hx.2 i,hy.2 i,hχ0,hη0,hdχ0,hdη0]

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
        ite_eq_right (not_lt_of_ge hn),he,hd,zero_apply,mul_zero,zero_mul,add_zero]
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
