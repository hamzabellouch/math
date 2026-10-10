import OAI.Analysis.AncientFlat.Evolution.SharpPrincipal

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ZeroAtInfty BoundedContinuousFunction SchwartzMap
namespace FrozenParametrix
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma exists_fullResidual_lipschitz_bound_sharp (α β : ℝ) (hα : 0 < α) (B L : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a₀ a₁ : C(V,Icc α β)) (b : V →ᵇ ℂ)
      (_hb : ‖b‖ ≤ B) (_hLipa : ∀ x y, |(a₁ x).val-(a₁ y).val| ≤ L*‖x-y‖)
      (_hLipb : ∀ x y, ‖b x-b y‖ ≤ L*‖x-y‖)
      (r q : ℝ) (_hr : 0 < r) (_hr1 : r ≤ 1) (_hq : 0≤q) (_hqr : q≤r)
      (_hc : ∀ x y, |(a₁ x).val-(a₀ y).val|≤L*(‖x-y‖+q)) (f : C₀(V,ℂ)) (x y : V),
      ‖fullResidualCLM hα a₀ a₁ b r f x-fullResidualCLM hα a₀ a₁ b r f y‖ ≤
        ((r⁻¹)^4*‖f‖*C)*‖x-y‖ := by
  obtain ⟨C,hC,hp⟩ := exists_principal_lipschitz_bound_sharp (V := V) α β hα L hL
  obtain ⟨D,hD,hf⟩ := exists_frozen_lipschitz_bound_sharp (V := V) α β hα B L hB hL
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro a₀ a₁ b hb ha hl r q hr hr1 hq hqr hc f x y
  have he : fullResidualCLM hα a₀ a₁ b r f x-fullResidualCLM hα a₀ a₁ b r f y =
      (principalResidual hα a₀ a₁ r f x-principalResidual hα a₀ a₁ r f y)+
      (b x*frozenOp hα a₀ r f x-b y*frozenOp hα a₀ r f y) := by
    simp only [fullResidualCLM_apply, ZeroAtInftyContinuousMap.add_apply, C0Multiplier.mul_apply]
    ring
  rw [he]
  calc
    _ ≤ ‖principalResidual hα a₀ a₁ r f x-principalResidual hα a₀ a₁ r f y‖+
      ‖b x*frozenOp hα a₀ r f x-b y*frozenOp hα a₀ r f y‖ := norm_add_le ..
    _ ≤ ((r⁻¹)^4*‖f‖*C)*‖x-y‖+((r⁻¹)^4*‖f‖*D)*‖x-y‖ :=
      add_le_add (hp a₀ a₁ r q hr hq hqr hc ha f x y) (hf a₀ b hb hl r hr hr1 f x y)
    _ = _ := by ring
end FrozenParametrix

namespace ParametrixVolterra
open scoped ZeroAtInfty BoundedContinuousFunction
open FrozenParametrix C0Convolution StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T, V →ᵇ Icc α β)) (b : C(Slab T, V →ᵇ ℂ))

lemma exists_actualResidual_holder_bound_sharp (hT : T ≤ 1) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hLipb : ∀ s : Slab T, ∀ x z : V, ‖b s x-b s z‖ ≤ L*‖x-z‖)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : Time T) (s : Slab T) (_hst : s.val<t.val)
      (f : C₀(V,ℂ)) (x y : V),
      ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
        C*‖f‖*(t.val-s.val)^(-(3+γ)/4)*‖x-y‖^γ := by
  obtain ⟨C,hC,hb₀⟩ := exists_actualResidual_bound hα A b hT L B hL hB hb hLip
  obtain ⟨D,hD,hb₁⟩ := exists_fullResidual_lipschitz_bound_sharp (V := V) α β hα B L hB hL
  refine ⟨2*C+D,by positivity,?_⟩
  intro t s hst f x y
  let q := t.val-s.val
  have hq : 0 < q := sub_pos.mpr hst
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [t.property.2,s.property.1]
  have hnorm (z : V) : ‖actualResidual hα A b t s f z‖ ≤ C*q^(-3/4 : ℝ)*‖f‖ :=
    ((actualResidual hα A b t s f).toBCF.norm_coe_le_norm z).trans
      (((actualResidual hα A b t s).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (hb₀ t s hst) (norm_nonneg f)))
  have hs : ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
      ((2*C+D)*‖f‖)*q^(-3/4 : ℝ) := by
    calc
      _ ≤ ‖actualResidual hα A b t s f x‖+‖actualResidual hα A b t s f y‖ := norm_sub_le ..
      _ ≤ C*q^(-3/4 : ℝ)*‖f‖+C*q^(-3/4 : ℝ)*‖f‖ := add_le_add (hnorm x) (hnorm y)
      _ ≤ _ := by nlinarith [mul_nonneg hD (mul_nonneg (norm_nonneg f) (Real.rpow_nonneg hq.le (-3/4 : ℝ)))]
  have hl : ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
      (((2*C+D)*‖f‖)*q^(-1 : ℝ))*‖x-y‖ := by
    have h := hb₁ (A s).toContinuousMap (A (now t)).toContinuousMap (b (now t)) (hb _)
      (fun z w => by
        change |(A (now t) z).val-(A (now t) w).val| ≤ L*‖z-w‖
        simpa only [sub_self,abs_zero,add_zero] using hLip (now t) (now t) z w)
      (hLipb _) (ParabolicRadius.radius q) q (ParabolicRadius.pos hq)
      (ParabolicRadius.le_one hq.le hq1) hq.le
      (by
        have hh := Real.rpow_le_rpow_of_exponent_ge hq hq1 (show (1/4:ℝ)≤1 by norm_num)
        simpa only [Real.rpow_one,ParabolicRadius.radius] using hh)
      (fun z w => by
        change |(A (now t) z).val-(A s w).val|≤L*(‖z-w‖+q)
        simpa only [now,q,abs_of_pos (sub_pos.mpr hst)] using hLip (now t) s z w) f x y
    rw [inv_pow,ParabolicRadius.pow_four hq.le,← Real.rpow_neg_one] at h
    apply h.trans
    calc
      _ = D*‖f‖*q^(-1 : ℝ)*‖x-y‖ := by ring
      _ ≤ _ := by gcongr; nlinarith
  convert HolderInterpolation.scaled (norm_nonneg _)
    (show 0 ≤ (2*C+D)*‖f‖ by positivity) (norm_nonneg (x-y)) hq hγ hγ1 hs hl using 1; dsimp only [q]; congr 2; ring_nf
end ParametrixVolterra

end

end OAI
