import OAI.Analysis.AncientFlat.Regularity.UniformSourceCorrection
import OAI.Analysis.AncientFlat.Regularity.GammaCorrection

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction
namespace ParametrixVolterra
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}
lemma norm_residual_integral_le (hα : 0 < α)
    (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
    (hT₀ : 0 ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ (t : Time T) (s : Slab T), s.val<t.val →
      ‖actualResidual hα A b t s‖ ≤ C*(t.val-s.val)^(-3/4 : ℝ))
    (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T) :
    ‖∫ r in 0..t.val, residualKernel hα A b hT₀ t r (unweighted j r)‖ ≤
      C*‖j‖*t.val^(-1/2 : ℝ)*(∫ s in 0..1, BetaWeights.density (3/4) (3/4) 1 s) := by
  calc
    _ ≤ ∫ r in 0..t.val, (C*‖j‖)*BetaWeights.density (3/4) (3/4) t.val r := by
      apply intervalIntegral.norm_integral_le_of_norm_le t.property.1.le
      · rw [←ae_restrict_iff' measurableSet_Ioc,←restrict_Ioo_eq_restrict_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        let s : Slab T := ⟨r,hr.1.le,hr.2.le.trans t.property.2⟩
        have he : projIcc 0 T hT₀ r=s := projIcc_of_mem hT₀ s.property
        simp only [residualKernel,ite_eq_left hr,he]
        calc
          _ ≤ C*(t.val-r)^(-3/4 : ℝ)*‖unweighted j r‖ :=
            ((actualResidual hα A b t s).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (hR t s hr.2) (norm_nonneg _))
          _ ≤ C*(t.val-r)^(-3/4 : ℝ)*(r^(-3/4 : ℝ)*‖j‖) := by
            apply mul_le_mul_of_nonneg_left (norm_unweighted_le j r hr.1)
            exact mul_nonneg hC (Real.rpow_nonneg (sub_pos.mpr hr.2).le _)
          _ = _ := by unfold BetaWeights.density; ring_nf
      · exact (BetaWeights.intervalIntegrable (3/4) (3/4) (by norm_num) (by norm_num) _ t.property.1).const_mul _
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,BetaWeights.integral_scale _ _ _ t.property.1]
      norm_num
      ring
lemma c0Time_sub (hα : 0<α) (a : V →ᵇ Icc α β) (q : ℝ) (f g : C₀(V,ℂ)) :
    c0Time hα a q (f-g)=c0Time hα a q f-c0Time hα a q g :=
  (frozenCLM hα a.toContinuousMap (ParabolicRadius.radius q)).map_sub f g

lemma norm_duhamel_sub_frozen_source_le (hα : 0<α)
    (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
    (hT₀ : 0 ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ (t : Time T) (s : Slab T), s.val<t.val →
      ‖actualResidual hα A b t s‖ ≤ C*(t.val-s.val)^(-3/4 : ℝ))
    (j : Time T →ᵇ C₀(V,ℂ)) (g : ℝ → C₀(V,ℂ)) (hg : Continuous g)
    (hj : ∀ t : Time T, unweighted j t.val+∫ r in 0..t.val,
      residualKernel hα A b hT₀ t r (unweighted j r)=g t.val)
    (t : Time T) :
    ‖duhamel hα A j t.val-∫ r in 0..t.val,
      c0Time hα (A (projIcc 0 T hT₀ r)) (t.val-r) (g r)‖ ≤
      2*frozenBound (V := V) (β := β) hα*C*‖j‖*
        (∫ s in 0..1, BetaWeights.density (3/4) (3/4) 1 s)*t.val^(1/2 : ℝ) := by
  let M := frozenBound (V := V) (β := β) hα
  let Q := ∫ s in (0:ℝ)..1, BetaWeights.density (3/4) (3/4) 1 s
  have hM : 0 ≤ M := frozenBound_nonneg hα
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg zero_le_one
    (fun r hr => BetaWeights.density_nonneg _ _ _ _ hr.1 hr.2)
  have hf : Continuous (fun r : ℝ => c0Time hα (A (projIcc 0 T hT₀ r)) (t.val-r) (g r)) :=
    continuous_c0Time_comp hα _ _ _ (A.continuous.comp continuous_projIcc)
      (continuous_const.sub continuous_id) hg
  rw [duhamel,←intervalIntegral.integral_sub
    (intervalIntegrable_sourceFrozen hα A j _ _ ⟨t.property.1.le,t.property.2⟩) (hf.intervalIntegrable 0 t.val)]
  calc
    _ ≤ ∫ r in 0..t.val, (M*C*‖j‖*Q)*r^(-1/2 : ℝ) := by
      apply intervalIntegral.norm_integral_le_of_norm_le t.property.1.le
      · rw [←ae_restrict_iff' measurableSet_Ioc,←restrict_Ioo_eq_restrict_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        let r₁ : Time T := ⟨r,hr.1,hr.2.le.trans t.property.2⟩
        have hrT : r ∈ Ioc (0:ℝ) T := r₁.property
        have he : projIcc 0 T hT₀ r=now r₁ := projIcc_of_mem hT₀ (now r₁).property
        rw [VolterraIntegral.sourceExtend_apply _ _ _ hrT,he]
        change ‖c0Time hα (A (now r₁)) (t.val-r) (unweighted j r)-
          c0Time hα (A (now r₁)) (t.val-r) (g r)‖ ≤ _
        rw [←c0Time_sub]
        have hjr : unweighted j r-g r = -(∫ s in 0..r,
            residualKernel hα A b hT₀ r₁ s (unweighted j s)) := by
          have hh := hj r₁
          change unweighted j r+_=_ at hh
          rw [←hh]; abel
        calc
          _ ≤ M*‖unweighted j r-g r‖ := norm_c0Time_le hα _ _ _
          _ = M*‖∫ s in 0..r, residualKernel hα A b hT₀ r₁ s (unweighted j s)‖ := by rw [hjr,norm_neg]
          _ ≤ M*(C*‖j‖*r^(-1/2 : ℝ)*Q) := mul_le_mul_of_nonneg_left
            (norm_residual_integral_le hα A b hT₀ C hC hR j r₁) hM
          _ = _ := by ring
      · exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -1/2)).const_mul _
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -1/2))]
      norm_num
      dsimp [M,Q]
      ring
end ParametrixVolterra

end

end OAI
