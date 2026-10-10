import OAI.Analysis.AncientFlat.Regularity.CorrectionSourceClassical

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParametrixEvolution
open ParametrixVolterra FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}
lemma exists_zero_source_response (hα : 0<α) (L B : ℝ) (hL : 0≤L) (hB : 0≤B)
    (A : C(ℝ,V →ᵇ Icc α β)) (b : C(ℝ,V →ᵇ ℂ))
    (R : ℝ) (hR : R≤1)
    (hb : ∀ s ∈ Icc 0 R, ‖b s‖≤B)
    (hLip : ∀ s ∈ Icc 0 R, ∀ r ∈ Icc 0 R, ∀ x z : V,
      |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s-r|))
    (hLipb : ∀ s ∈ Icc 0 R, ∀ x z : V, ‖b s x-b s z‖≤L*‖x-z‖)
    (hA : ∀ s ∈ Icc 0 R, ContDiff ℝ ∞ (fun x => (A s x).val))
    (γ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc 0 R, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^γ) :
    ∃ E : ℝ, 0≤E ∧ ∀ T : ℝ, 0<T → T≤R →
      ∃ u : ℝ → C₀(V,ℂ), SourceEvolves A b f 0 T 0 u ∧
        ‖u T-∫ r in (0:ℝ)..T, c0Time hα (A r) (T-r) (f r)‖≤E*T^(5/4 : ℝ) := by
  obtain ⟨C,D,hC,hD,hcorr⟩ := exists_uniform_source_correction (V := V) (β := β) hα L B hL hB
  obtain ⟨N,hN,hres⟩ := exists_uniform_fullResidual_bound (V := V) α β hα L B hL hB
  let M := frozenBound (V := V) (β := β) hα
  let Q := ∫ s in (0:ℝ)..1, BetaWeights.density (3/4) (3/4) 1 s
  have hM : 0≤M := frozenBound_nonneg hα
  have hQ : 0≤Q := intervalIntegral.integral_nonneg zero_le_one
    (fun r hr => BetaWeights.density_nonneg _ _ _ _ hr.1 hr.2)
  refine ⟨2*M*N*D*‖f‖*Q,by positivity,fun T hT hTR => ?_⟩
  let incl : C(Slab T,ℝ) := ⟨Subtype.val,continuous_subtype_val⟩
  let A' := A.comp incl
  let b' := b.comp incl
  let l : Time T →ᵇ C₀(V,ℂ) := f.compContinuous ⟨Subtype.val,continuous_subtype_val⟩
  have hprim (r : Slab T) : r.val ∈ Icc 0 R := ⟨r.property.1,r.property.2.trans hTR⟩
  have hLip' : ∀ s r : Slab T, ∀ x z : V,
      |(A' s x).val-(A' r z).val|≤L*(‖x-z‖+|s.val-r.val|) :=
    fun s r => hLip s.val (hprim s) r.val (hprim r)
  have hT1 : T≤1 := hTR.trans hR
  obtain ⟨j,hi,hj,hjb⟩ := hcorr T hT.le hT1 A' b' (fun r => hb r.val (hprim r)) hLip' 0 l
  obtain ⟨H,hH,hfH⟩ := hf
  have hl : ∃ H : ℝ, 0≤H ∧ ∀ t x y, ‖l t x-l t y‖≤H*‖x-y‖^γ :=
    ⟨H,hH,fun t x y => hfH t.val ⟨t.property.1.le,t.property.2.trans hTR⟩ x y⟩
  obtain ⟨huc,huJ,hut⟩ := correction_source_classical hα A' b' hT.le hT1 L B hL hB
    (fun r => hb r.val (hprim r)) hLip' (fun r => hLipb r.val (hprim r))
    (fun r => hA r.val (hprim r)) γ hγ hγ1 0 l j hl hi hj
  let u := mildTime hα A' hT.le 0 j
  have hu : SourceEvolves A b f 0 T 0 u := by
    refine ⟨mildTime_zero hα A' hT.le 0 j,continuousOn_mildTime hα A' hT.le 0 j,huc,huJ,?_⟩
    intro t ht
    exact hut ⟨t,ht.1,ht.2.le⟩ ht.2
  refine ⟨u,hu,?_⟩
  have hRj : ∀ (t : Time T) (s : Slab T), s.val<t.val →
      ‖actualResidual hα A' b' t s‖≤N*(t.val-s.val)^(-3/4 : ℝ) := by
    intro t s hst
    have hq : 0<t.val-s.val := sub_pos.mpr hst
    have hq1 : t.val-s.val≤1 := by linarith [t.property.2,s.property.1]
    have he : |(now t).val-s.val|=ParabolicRadius.radius (t.val-s.val)^4 := by
      rw [ParabolicRadius.pow_four hq.le]
      exact abs_of_pos hq
    unfold actualResidual
    rw [←ParabolicRadius.inv_pow_three hq.le]
    apply hres _ _ _ _ (ParabolicRadius.pos hq) (ParabolicRadius.le_one hq.le hq1) (hb _ (hprim _))
    intro x z
    simpa only [he,BoundedContinuousFunction.coe_toContinuousMap] using hLip' (now t) s x z
  have hje : ∀ t : Time T, unweighted j t.val+∫ r in 0..t.val,
      residualKernel hα A' b' hT.le t r (unweighted j r)=f t.val := by
    intro t
    simpa only [map_zero,sub_zero,l,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk] using hj t
  have hh := norm_duhamel_sub_frozen_source_le hα A' b' hT.le N hN hRj j f f.continuous hje ⟨T,hT,le_rfl⟩
  have he : (∫ r in (0:ℝ)..T, c0Time hα (A' (projIcc 0 T hT.le r)) (T-r) (f r))=
      ∫ r in (0:ℝ)..T, c0Time hα (A r) (T-r) (f r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hT.le] at hr
    have hp := congrArg Subtype.val (projIcc_of_mem hT.le hr)
    change c0Time hα (A (projIcc 0 T hT.le r).val) (T-r) (f r)=_
    rw [hp]
  have huT : u T=duhamel hα A' j T := by
    change c0Time hα (A' (initial hT.le)) T 0+_= _
    have hz : c0Time hα (A' (initial hT.le)) T 0=0 := (frozenCLM hα _ _).map_zero
    rw [hz,zero_add]
  rw [huT]
  change ‖_ - _‖≤_
  simpa only [he] using (hh.trans (show 2*M*N*‖j‖*Q*T^(1/2 : ℝ)≤
      (2*M*N*D*‖f‖*Q)*T^(5/4 : ℝ) from by
    have hjb' : ‖j‖≤D*(T^(3/4 : ℝ)*‖f‖) := by
      apply hjb.trans
      simp only [norm_zero,mul_zero,zero_add]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (BoundedContinuousFunction.norm_compContinuous_le _ _) (Real.rpow_nonneg hT.le _)) hD.le
    calc
      _≤2*M*N*(D*(T^(3/4 : ℝ)*‖f‖))*Q*T^(1/2 : ℝ) := by gcongr
      _=(2*M*N*D*‖f‖*Q)*(T^(3/4 : ℝ)*T^(1/2 : ℝ)) := by ring
      _=_ := by rw [←Real.rpow_add hT]; norm_num))
end ParametrixEvolution

end

end OAI
