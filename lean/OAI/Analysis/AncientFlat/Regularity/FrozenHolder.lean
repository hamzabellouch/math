import OAI.Analysis.AncientFlat.Evolution.VariableRows
import OAI.Analysis.AncientFlat.Regularity.LocalHolder

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BoundedContinuousFunction SchwartzMap
namespace VariableSchauder
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma frozen_fourth_holder (K : SchwartzMap V ℂ) (A : V → ℝ) (hA : Continuous A)
    (α β L γ a T : ℝ) (hα : 0<α) (hL : 0≤L) (hγ : 0<γ) (hγ1 : γ<1)
    (ha : 0<a) (hT : T≤1) (hAr : ∀ y,A y∈Icc α β)
    (hAL : ∀ x y, ‖A x-A y‖≤L*‖x-y‖) (f : V →ᵇ ℂ) :
    ∃ C : ℝ, 0≤C ∧ (∀ t∈Icc a T, ∀ x, ‖jet K A t f 4 x‖≤C) ∧
      ∀ t∈Icc a T, ∀ s∈Icc a T, ∀ x y,
        ‖jet K A t f 4 x-jet K A s f 4 y‖≤C*(‖x-y‖^γ+|t-s|^(γ/4)) := by
  have hhh (x y : V) : ‖f x-f y‖≤(2*‖f‖)*‖x-y‖^(0:ℝ) := by
    simp only [Real.rpow_zero,mul_one]
    exact (norm_sub_le ..).trans ((add_le_add (f.norm_coe_le_norm x) (f.norm_coe_le_norm y)).trans_eq (by ring))
  have hαβ : α≤β := (hAr 0).1.trans (hAr 0).2
  obtain ⟨C,hC,hcn⟩ := exists_jet_bound (V := V) K 4 (by norm_num) α β 0 L hα le_rfl (by norm_num) hL
  obtain ⟨D,hD,hdl⟩ := exists_jet_lipschitz (V := V) K 4 α β 0 L hα le_rfl (by norm_num) hL
  obtain ⟨E,hE,het⟩ := exists_jet_time_increment (V := V) K 4 (by norm_num) α β 0 L hα hαβ le_rfl (by norm_num) hL
  have hcn' := hcn A hA hAr hAL f (2*‖f‖) ‖f‖ (by positivity) (norm_nonneg _) le_rfl hhh
  have hdl' := hdl A hA hAr hAL f (2*‖f‖) ‖f‖ (by positivity) (norm_nonneg _) le_rfl hhh
  have het' := het A hA hAr hAL f (2*‖f‖) ‖f‖ (by positivity) (norm_nonneg _) le_rfl hhh
  norm_num only [Nat.cast_ofNat,zero_sub,neg_div] at hcn' hdl' het'
  apply LocalHolder.of_lipschitz (fun t x => jet K A t f 4 x) a T γ ha hγ hγ1
    (C*(2*‖f‖+‖f‖)*a^(-1:ℝ)) (D*(2*‖f‖+‖f‖)*a^(-(5/4):ℝ))
    (E*(2*‖f‖+‖f‖)*a^(-2:ℝ)) (by positivity) (by positivity) (by positivity)
  · intro t ht x
    have hp : t^(-1:ℝ)≤a^(-1:ℝ) := Real.rpow_le_rpow_of_nonpos ha ht.1 (by norm_num)
    exact (hcn' t (ha.trans_le ht.1) (ht.2.trans hT) x).trans
      (mul_le_mul_of_nonneg_left hp (by positivity))
  · intro t ht x y
    have hp : t^(-(5/4):ℝ)≤a^(-(5/4):ℝ) := Real.rpow_le_rpow_of_nonpos ha ht.1 (by norm_num)
    exact (hdl' t (ha.trans_le ht.1) (ht.2.trans hT) x y).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (norm_nonneg _))
  · intro s hs t ht hst hts x
    have he := het' s (t-s) (ha.trans_le hs.1) (hs.2.trans hT) (sub_nonneg.mpr hst) (hts.trans hs.1) x
    rw [add_sub_cancel] at he
    have hp : s^(-2:ℝ)≤a^(-2:ℝ) := Real.rpow_le_rpow_of_nonpos ha hs.1 (by norm_num)
    calc
      _ ≤ E*(2*‖f‖+‖f‖)*(t-s)*s^(-2:ℝ) := he
      _ ≤ E*(2*‖f‖+‖f‖)*(t-s)*a^(-2:ℝ) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
end VariableSchauder

end

end OAI
