import OAI.Analysis.AncientFlat.Regularity.ConstantResidual
import OAI.Analysis.AncientFlat.Regularity.CorrectionSourceClassical
import OAI.Analysis.AncientFlat.Regularity.SchauderKernel

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicSchauder
open ParametrixVolterra FrozenParametrix StrongWeightedVolterra ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def unitLine : C(ℝ,V →ᵇ Icc (1:ℝ) 1) := ⟨fun _ => unitCoefficient,continuous_const⟩
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma unitLine_jets (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => ((unitLine (V := V)) 0 y).val) x‖≤1 := by
  change ‖iteratedFDeriv ℝ n (fun _ : V => (1:ℝ)) x‖≤1
  cases n with
  | zero => simp
  | succ n => simp [iteratedFDeriv_succ_const]
lemma frozen_integral_apply (_T t : ℝ) (ht : 0≤t)
    (f : ℝ →ᵇ C₀(V,ℂ)) (x : V) :
    (∫ r in 0..t, c0Time zero_lt_one (unitCoefficient (V := V)) (t-r) (f r)) x=
      potential (fun r => (f r).toBCF) t x := by
  have hc : Continuous (fun r : ℝ => c0Time zero_lt_one (unitCoefficient (V := V)) (t-r) (f r)) :=
    continuous_c0Time_comp zero_lt_one _ _ _ continuous_const
      (continuous_const.sub continuous_id) f.continuous
  have he := (C0Convolution.eval x).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 t)
  simp only [C0Convolution.eval_apply] at he
  rw [←he]
  rw [intervalIntegral.integral_of_le ht,integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact unit_c0Time _ (sub_pos.mpr hr.2) (f r) x

theorem constant_representation {T γ : ℝ} (hT : 0≤T) (hT1 : T≤1)
    (hγ : 0<γ) (hγ1 : γ≤1) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t∈Icc 0 T, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^γ)
    (u : ℝ → C₀(V,ℂ)) (hu : SourceEvolves unitLine 0 f 0 T 0 u) :
    ∀ t∈Icc 0 T, ∀ x, u t x=potential (fun r => (f r).toBCF) t x := by
  let A := unitSlab (V := V) T
  let l : Time T →ᵇ C₀(V,ℂ) := f.compContinuous ⟨Subtype.val,continuous_subtype_val⟩
  have hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val|≤0*(‖x-z‖+|s.val-r.val|) := by
    intros; simp [A,unitSlab,unitCoefficient]
  have hb : ∀ s : Slab T, ‖(0 : C(Slab T,V →ᵇ ℂ)) s‖≤0 := by simp
  have hLipb : ∀ s : Slab T, ∀ x z : V,
      ‖(0 : C(Slab T,V →ᵇ ℂ)) s x-(0 : C(Slab T,V →ᵇ ℂ)) s z‖≤0*‖x-z‖ := by simp
  have hA : ∀ s : Slab T, ContDiff ℝ ∞ (fun x => (A s x).val) := by
    intro s; exact contDiff_const
  obtain ⟨C,D,hC,hD,hs⟩ := exists_parametrix_correction_full zero_lt_one A 0 hT hT1
    0 0 le_rfl le_rfl hb hLip
  obtain ⟨j,hi,hj,_⟩ := hs 0 l
  have hl : ∃ H : ℝ, 0≤H ∧ ∀ t x y, ‖l t x-l t y‖≤H*‖x-y‖^γ := by
    obtain ⟨H,hH,hf⟩ := hf
    exact ⟨H,hH,fun t => hf t.val ⟨t.property.1.le,t.property.2⟩⟩
  obtain ⟨hvc,hvJ,hvt⟩ := correction_source_classical zero_lt_one A 0 hT hT1
    0 0 le_rfl le_rfl hb hLip hLipb hA γ hγ hγ1 0 l j hl hi hj
  let v := mildTime zero_lt_one A hT 0 j
  have hv : SourceEvolves unitLine 0 f 0 T 0 v := by
    refine ⟨mildTime_zero zero_lt_one A hT 0 j,
      continuousOn_mildTime zero_lt_one A hT 0 j,hvc,hvJ,?_⟩
    intro t ht
    exact hvt ⟨t,ht.1,ht.2.le⟩ ht.2
  have huv : ∀ t∈Icc 0 T, u t=v t := hu.unique hv hT zero_lt_one (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)≤0) (by simp) (fun _ _ => contDiff_const)
    (fun _ _ n _ x => unitLine_jets n x)
  intro t ht x
  rw [huv t ht]
  by_cases ht0 : t=0
  · subst t
    rw [hv.1]
    simp [potential]
  · have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hje : ∀ t : Time T, unweighted j t.val+∫ r in 0..t.val,
        residualKernel zero_lt_one A 0 hT t r (unweighted j r)=f t.val := by
      intro t
      simpa only [map_zero,sub_zero,l,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk] using hj t
    have hR : ∀ (t : Time T) (s : Slab T), s.val<t.val →
        ‖actualResidual zero_lt_one A 0 t s‖≤0*(t.val-s.val)^(-3/4 : ℝ) := by
      intro t s _
      rw [show actualResidual zero_lt_one A 0 t s=0 from unit_residual_zero t s,zero_mul]
      exact le_of_eq (ContinuousLinearMap.opNorm_zero)
    have hh := norm_duhamel_sub_frozen_source_le zero_lt_one A 0 hT 0 le_rfl hR j f f.continuous hje ⟨t,htp,ht.2⟩
    have he : duhamel zero_lt_one A j t=∫ r in 0..t,
        c0Time zero_lt_one unitCoefficient (t-r) (f r) := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa [A,unitSlab] using hh
    have hvd : v t=duhamel zero_lt_one A j t := by
      change c0Time zero_lt_one (A (initial hT)) t 0+_= _
      have hz : c0Time zero_lt_one (A (initial hT)) t 0=0 := (frozenCLM zero_lt_one _ _).map_zero
      rw [hz,zero_add]
    rw [hvd,he,frozen_integral_apply T t ht.1 f x]
end ParabolicSchauder

end

end OAI
