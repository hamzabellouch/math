import OAI.Analysis.AncientFlat.Evolution.BetaRow
import OAI.Analysis.AncientFlat.Regularity.GammaCorrection

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology ZeroAtInfty BoundedContinuousFunction ContDiff
namespace SourceFrozenRows
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}
lemma exists_timeBCF_four_bound_gamma (K : SchwartzMap V ℂ) (hα : 0 < α) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (a : V →ᵇ Icc α β) (L : ℝ) (_hL : 0 ≤ L)
        (_hLip : ∀ x y, ‖(a x).val-(a y).val‖ ≤ L*‖x-y‖)
        (f : V →ᵇ ℂ) (H : ℝ) (_hH : 0 ≤ H)
        (_hhold : ∀ x y, ‖f x-f y‖ ≤ H*‖x-y‖^γ)
        (q : ℝ) (hq : 0 < q),
        ‖timeBCF K hα a q hq f 4‖ ≤ H*C*q^(-(1-γ/4) : ℝ)+‖f‖*L*D*q^(-3/4 : ℝ) := by
  obtain ⟨C,D,hC,hD,hb⟩ := exists_row_holder_bound K 4 (by omega) α β hα γ hγ.le hγ1
  refine ⟨C,D,hC,hD,?_⟩
  intro a L hL hLip f H hH hhold q hq
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  rw [timeBCF_apply]
  have h := hb (fun y => (a y).val) (continuous_subtype_val.comp a.continuous)
    (fun y => (a y).property) L hL hLip f H hH hhold (q^(1/4 : ℝ)) (Real.rpow_pos_of_pos hq (1/4)) x
  apply h.trans_eq
  have h1 := radius_weight q hq 4 γ
  have h2 := radius_weight q hq 4 1
  norm_num only [Nat.cast_ofNat] at h1 h2
  rw [Real.rpow_one] at h2
  calc
    _ = H*C*((q^(1/4 : ℝ))⁻¹^4*(q^(1/4 : ℝ))^γ)+
        ‖f‖*L*D*((q^(1/4 : ℝ))⁻¹^4*q^(1/4 : ℝ)) := by ring
    _ = _ := by rw [h1,h2]; congr 2 <;> congr 1 <;> ring
end SourceFrozenRows

namespace ParametrixVolterra
open SourceFrozenRows StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (K : SchwartzMap V ℂ) (hα : 0 < α)
  (A : C(Slab T,V →ᵇ Icc α β)) (j : Time T →ᵇ C₀(V,ℂ))
lemma exists_rowData_bound_gamma (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (L H : ℝ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hLip : ∀ s : Slab T, ∀ x y, ‖(A s x).val-(A s y).val‖ ≤ L*‖x-y‖)
    (hhold : ∀ s : Time T, ∀ x y, ‖unweighted j s.val x-unweighted j s.val y‖ ≤
      H*s.val^(-7/8 : ℝ)*‖x-y‖^γ)
    (a : ℝ) (ha : 0 < a) :
    ∃ b : UnitTime → ℝ, Integrable b ∧ ∀ t : Time T, a ≤ t.val →
      ∀ u, ‖rowData K hα A j t u‖ ≤ b u := by
  obtain ⟨C,D,hC,hD,hb⟩ := exists_timeBCF_four_bound_gamma (β := β) K hα γ hγ hγ1
  let b : UnitTime → ℝ := fun u =>
    H*C*a^(-7/8 : ℝ)*a^(-(1-γ/4) : ℝ)*BetaWeights.density (7/8) ((1-γ/4)) 1 u.val+
    ‖j‖*L*D*a^(-3/4 : ℝ)*a^(-3/4 : ℝ)*BetaWeights.density (3/4) (3/4) 1 u.val
  refine ⟨b,?_,?_⟩
  · exact ((integrable_beta_unit (7/8) ((1-γ/4)) (by norm_num) (by linarith)).const_mul _).add
      ((integrable_beta_unit (3/4) (3/4) (by norm_num) (by norm_num)).const_mul _)
  · intro t ht u
    have hs := (lag t u).property.1
    have htpos := t.property.1
    have hup := u.property.1
    have hum := sub_pos.mpr u.property.2
    have hq : 0 < t.val*(1-u.val) := mul_pos t.property.1 (sub_pos.mpr u.property.2)
    have hn := norm_unweighted_le j (lag t u).val hs
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at hn
    have hrow := hb (A (now (lag t u))) L hL (hLip _) (unweighted j (lag t u).val).toBCF
      (H*(lag t u).val^(-7/8 : ℝ)) (by positivity) (hhold (lag t u)) _ hq
    have hnorm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hL) hD)
      (Real.rpow_nonneg hq.le (-3/4))
    refine hrow.trans ((add_le_add le_rfl hnorm).trans ?_)
    dsimp only [lag, b, BetaWeights.density]
    rw [Real.mul_rpow t.property.1.le u.property.1.le,
      Real.mul_rpow t.property.1.le (sub_pos.mpr u.property.2).le,
      Real.mul_rpow t.property.1.le u.property.1.le,
      Real.mul_rpow t.property.1.le (sub_pos.mpr u.property.2).le]
    have ht1 := Real.rpow_le_rpow_of_nonpos ha ht (by norm_num : (-7/8 : ℝ) ≤ 0)
    have ht2 := Real.rpow_le_rpow_of_nonpos ha ht (by linarith : (-(1-γ/4) : ℝ) ≤ 0)
    have ht3 := Real.rpow_le_rpow_of_nonpos ha ht (by norm_num : (-3/4 : ℝ) ≤ 0)
    simp only [neg_div]
    calc
      _ = H*C*(t.val^(-7/8 : ℝ)*t.val^(-(1-γ/4) : ℝ))*
          (u.val^(-7/8 : ℝ)*(1-u.val)^(-(1-γ/4) : ℝ))+
          ‖j‖*L*D*(t.val^(-3/4 : ℝ)*t.val^(-3/4 : ℝ))*
          (u.val^(-3/4 : ℝ)*(1-u.val)^(-3/4 : ℝ)) := by ring_nf
      _ ≤ H*C*(a^(-7/8 : ℝ)*a^(-(1-γ/4) : ℝ))*
          (u.val^(-7/8 : ℝ)*(1-u.val)^(-(1-γ/4) : ℝ))+
          ‖j‖*L*D*(a^(-3/4 : ℝ)*a^(-3/4 : ℝ))*
          (u.val^(-3/4 : ℝ)*(1-u.val)^(-3/4 : ℝ)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul ht1 ht2 (by positivity) (by positivity)) (by positivity)) (by positivity)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul ht3 ht3 (by positivity) (by positivity)) (by positivity)) (by positivity)
      _ = _ := by ring_nf
end ParametrixVolterra

end

end OAI
