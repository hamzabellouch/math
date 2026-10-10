import OAI.Analysis.AncientFlat.Regularity.SharpResidual

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ZeroAtInfty BoundedContinuousFunction SchwartzMap ContDiff
namespace ParametrixVolterra
section HolderResidualIntegralSharp
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
variable {γ p : ℝ}
lemma holder_residual_integral_sharp (hT₀ : 0 ≤ T) (hp : p<1) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ (t : Time T) (s : Slab T), s.val<t.val → ∀ (f : C₀(V,ℂ)) (x y : V),
      ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
        C*‖f‖*(t.val-s.val)^(-p)*‖x-y‖^γ)
    (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T)
    (hi : IntervalIntegrable (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val)
    (x y : V) :
    ‖(∫ r in 0..t.val, residualKernel hα A b hT₀ t r (unweighted j r)) x-
      (∫ r in 0..t.val, residualKernel hα A b hT₀ t r (unweighted j r)) y‖ ≤
      (C*‖j‖)*t.val^(1/4-p)*(∫ s in 0..1, BetaWeights.density (3/4) p 1 s)*‖x-y‖^γ := by
  have hh := HolderIntegral.beta_holder (x := x) (y := y)
    (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) t.val t.property.1 hi
    (3/4) p (by norm_num) hp (C*‖j‖) (‖x-y‖^γ)
  apply (show 1-(3/4 : ℝ)-p = 1/4-p by ring) ▸ hh
  intro r hr
  let s : Slab T := ⟨r,hr.1.le,hr.2.le.trans t.property.2⟩
  have he : projIcc 0 T hT₀ r = s := projIcc_of_mem hT₀ s.property
  have hu : ‖unweighted j r‖ ≤ r^(-3/4 : ℝ)*‖j‖ := by
    let u : Time T := ⟨r,hr.1,hr.2.le.trans t.property.2⟩
    change ‖unweighted j u.val‖ ≤ _
    rw [unweighted_at_time,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr.1.le _)]
    exact mul_le_mul_of_nonneg_left (j.norm_coe_le_norm u) (Real.rpow_nonneg hr.1.le _)
  simp only [residualKernel,ite_eq_left hr,he]
  calc
    _ ≤ C*‖unweighted j r‖*(t.val-r)^(-p)*‖x-y‖^γ := hR t s hr.2 _ x y
    _ ≤ C*(r^(-3/4 : ℝ)*‖j‖)*(t.val-r)^(-p)*‖x-y‖^γ := by
      gcongr
      exact Real.rpow_nonneg (sub_nonneg.mpr hr.2.le) _
    _ = _ := by unfold BetaWeights.density; ring_nf

lemma correction_holder_sharp (hT₀ : 0 ≤ T) (hT : T ≤ 1) (hp₀ : 0≤p) (hp₁ : p<1) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ (t : Time T) (s : Slab T), s.val<t.val → ∀ (f : C₀(V,ℂ)) (x y : V),
      ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
        C*‖f‖*(t.val-s.val)^(-p)*‖x-y‖^γ)
    (d : C₀(V,ℂ)) (l j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0 ≤ H)
    (hl : ∀ t x y, ‖l t x-l t y‖ ≤ H*‖x-y‖^γ)
    (hi : ∀ t : Time T, IntervalIntegrable
      (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val)
    (hj : ∀ t : Time T, unweighted j t.val + ∫ r in 0..t.val,
      residualKernel hα A b hT₀ t r (unweighted j r) = l t-actualResidual hα A b t (initial hT₀) d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : Time T, ∀ x y,
      ‖unweighted j t.val x-unweighted j t.val y‖ ≤ D*t.val^(-p)*‖x-y‖^γ := by
  let Q := ∫ s in 0..1, BetaWeights.density (3/4) p 1 s
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
    (fun s hs => BetaWeights.density_nonneg _ _ _ _ hs.1 hs.2)
  refine ⟨H+C*‖d‖+C*‖j‖*Q,by positivity,fun t x y => ?_⟩
  let v := ∫ r in 0..t.val, residualKernel hα A b hT₀ t r (unweighted j r)
  have he : unweighted j t.val = l t-actualResidual hα A b t (initial hT₀) d-v :=
    eq_sub_of_add_eq (hj t)
  have hd := hR t (initial hT₀) t.property.1 d x y
  simp only [initial,sub_zero] at hd
  have hv := holder_residual_integral_sharp hα A b hT₀ hp₁ C hC hR j t (hi t) x y
  have ht1 : t.val ≤ 1 := t.property.2.trans hT
  have hp : 1 ≤ t.val^(-p) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos t.property.1 ht1 (by linarith)
  have hq : t.val^(1/4-p) ≤ t.val^(-p) :=
    Real.rpow_le_rpow_of_exponent_ge t.property.1 ht1 (by linarith)
  rw [he]
  change ‖(l t x-actualResidual hα A b t (initial hT₀) d x-v x)-
    (l t y-actualResidual hα A b t (initial hT₀) d y-v y)‖ ≤ _
  calc
    _ = ‖(l t x-l t y)-(actualResidual hα A b t (initial hT₀) d x-
      actualResidual hα A b t (initial hT₀) d y)-(v x-v y)‖ := by congr 1; ring
    _ ≤ ‖l t x-l t y‖+‖actualResidual hα A b t (initial hT₀) d x-
      actualResidual hα A b t (initial hT₀) d y‖+‖v x-v y‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ H*‖x-y‖^γ+C*‖d‖*t.val^(-p)*‖x-y‖^γ+
      (C*‖j‖)*t.val^(1/4-p)*Q*‖x-y‖^γ := add_le_add (add_le_add (hl t x y) hd) hv
    _ ≤ H*t.val^(-p)*‖x-y‖^γ+C*‖d‖*t.val^(-p)*‖x-y‖^γ+
      (C*‖j‖)*t.val^(-p)*Q*‖x-y‖^γ := by gcongr; exact le_mul_of_one_le_right hH hp
    _ = _ := by ring
end HolderResidualIntegralSharp
open FrozenParametrix StrongWeightedVolterra
open scoped ZeroAtInfty BoundedContinuousFunction
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T,V →ᵇ Set.Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
theorem source_correction_holder_full (hT₀ : 0 ≤ T) (hT : T ≤ 1) (L B : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hLipb : ∀ s : Slab T, ∀ x z : V, ‖b s x-b s z‖ ≤ L*‖x-z‖)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (d : C₀(V,ℂ)) (l j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0 ≤ H)
    (hl : ∀ t x y, ‖l t x-l t y‖ ≤ H*‖x-y‖^γ)
    (hi : ∀ t : Time T, IntervalIntegrable
      (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) MeasureTheory.volume 0 t.val)
    (hj : ∀ t : Time T, unweighted j t.val + ∫ r in 0..t.val,
      residualKernel hα A b hT₀ t r (unweighted j r) = l t-actualResidual hα A b t (initial hT₀) d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : Time T, ∀ x y,
      ‖unweighted j t.val x-unweighted j t.val y‖ ≤ D*t.val^(-(3+γ)/4)*‖x-y‖^γ := by
  obtain ⟨C,hC,hR⟩ := exists_actualResidual_holder_bound_sharp hα A b hT L B hL hB hb hLip hLipb γ hγ hγ1
  simpa only [neg_div] using correction_holder_sharp hα A b hT₀ hT (by linarith : 0≤(3+γ)/4)
    (by linarith : (3+γ)/4<1) C hC (by simpa only [neg_div] using hR) d l j H hH hl hi hj
end ParametrixVolterra

end

end OAI
