import OAI.Analysis.AncientFlat.Evolution.VariableSpace

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BoundedContinuousFunction SchwartzMap
namespace MeasurableSchauder
open SourceFrozenRows ParabolicSchauder VariableSchauder
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (A : ℝ → V → ℝ) (hA : Continuous (Function.uncurry A))
  (α β L : ℝ) (hα : 0<α) (hAr : ∀ r y, A r y∈Icc α β)
  (hL : 0≤L) (hAL : ∀ r x y, ‖A r x-A r y‖≤L*‖x-y‖)
include hA hα hAr hL hAL in
lemma integrable_jet (K : SchwartzMap V ℂ) (f : ℝ → (V →ᵇ ℂ)) (hf : StronglyMeasurable f)
    (γ H M t : ℝ) (hγ : 0<γ) (hγ1 : γ≤1) (hH : 0≤H) (hM : 0≤M) (ht : 0≤t)
    (hm : ∀ r∈Ioo 0 t, ‖f r‖≤M)
    (hh : ∀ r ∈ Ioo 0 t, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^γ)
    (j : ℕ) (hj : j≤4) (x : V) :
    IntegrableOn (fun r => jet K (A r) (t-r) (f r) j x) (Ioo 0 t) := by
  rcases ht.eq_or_lt with he|ht
  · subst t; simp
  apply WeightedSourceFrozenRows.integrableOn_row K A hA α β hα hAr L hL hAL f hf 0 0 M H γ t
    (by norm_num) (by norm_num) hM hH ht hγ hγ1
    (by simpa using hm) (by simpa using hh) j hj x
include hα hL in
lemma exists_fourth_spatial_holder (K : SchwartzMap V ℂ) (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ B : ℝ, 0≤B ∧ ∀ (A : ℝ → V → ℝ), Continuous (Function.uncurry A) →
      (∀ r y, A r y∈Icc α β) → (∀ r x y, ‖A r x-A r y‖≤L*‖x-y‖) →
      ∀ (f : ℝ → (V →ᵇ ℂ)) (_ : StronglyMeasurable f) (H M t : ℝ), 0≤H → 0≤M → 0≤t → t≤1 →
      (∀ r∈Ioo 0 t, ‖f r‖≤M) →
      (∀ r ∈ Ioo 0 t, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^γ) → ∀ x y,
      ‖integratedJet K A f t 4 x-integratedJet K A f t 4 y‖≤B*(H+M)*‖x-y‖^γ := by
  obtain ⟨C,hC,hb⟩ := exists_jet_bound K 4 (by norm_num) α β γ L hα hγ.le hγ1.le hL
  obtain ⟨D,hD,hd⟩ := exists_jet_lipschitz K 4 α β γ L hα hγ.le hγ1.le hL
  let a := γ/4
  let b := (γ-1)/4
  have ha : 0<a := by dsimp [a]; positivity
  have hb0 : b<0 := by dsimp [b]; linarith
  have hneg : D/b≤0 := div_nonpos_of_nonneg_of_nonpos hD hb0.le
  have hpos : 0≤2*C/a := by positivity
  refine ⟨2*C/a-D/b,sub_nonneg.mpr (hneg.trans hpos),?_⟩
  intro A hA hAr hAL f hf H M t hH hM ht ht1 hm hh x y
  by_cases hxy : x=y
  · subst y; simp only [sub_self,norm_zero,Real.zero_rpow hγ.ne',mul_zero,le_refl]
  have hq : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let q := ‖x-y‖
  have hi (x : V) := integrable_jet A hA α β L hα hAr hL hAL K f hf γ H M t hγ hγ1.le hH hM ht hm hh 4 le_rfl x
  unfold integratedJet
  rw [← integral_sub (hi x) (hi y)]
  have he := norm_integral_lag_split a b (2*C*(H+M)) (D*(H+M)*q) (q^4) t ha hb0
    (by positivity) (by positivity) (by positivity) ht
    (fun r => jet K (A r) (t-r) (f r) 4 x-jet K (A r) (t-r) (f r) 4 y)
    ((hi x).sub (hi y)).aestronglyMeasurable
    (fun r hr _ => by
      calc
        _ ≤ ‖jet K (A r) (t-r) (f r) 4 x‖+‖jet K (A r) (t-r) (f r) 4 y‖ := norm_sub_le ..
        _ ≤ C*(H+M)*(t-r)^((γ-4)/4)+C*(H+M)*(t-r)^((γ-4)/4) := add_le_add
          (by simpa using hb (A r) (hA.comp (continuous_const.prodMk continuous_id)) (hAr r) (hAL r) (f r) H M hH hM (hm r hr) (hh r hr) (t-r) (sub_pos.mpr hr.2) (by linarith [hr.1]) x)
          (by simpa using hb (A r) (hA.comp (continuous_const.prodMk continuous_id)) (hAr r) (hAL r) (f r) H M hH hM (hm r hr) (hh r hr) (t-r) (sub_pos.mpr hr.2) (by linarith [hr.1]) y)
        _ = _ := by rw [show (γ-4)/4=a-1 by dsimp [a]; ring]; ring)
    (fun r hr _ => by
      convert hd (A r) (hA.comp (continuous_const.prodMk continuous_id)) (hAr r) (hAL r) (f r) H M hH hM (hm r hr) (hh r hr) (t-r) (sub_pos.mpr hr.2) (by linarith [hr.1]) x y using 1
      simp only [b,q,Nat.cast_ofNat]; rw [show (γ-(4+1))/4=(γ-1)/4-1 by ring]; ring)
  have hpa : (q^4)^a=q^γ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hq)]
    congr 1; dsimp [a]; ring
  have hpb : q*(q^4)^b=q^γ := by
    calc
      _ = q^1*q^(4*b) := by rw [Real.rpow_one,← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hq)]; norm_num; exact Or.inl rfl
      _ = q^(1+4*b) := (Real.rpow_add hq 1 (4*b)).symm
      _ = _ := by congr 1; dsimp [b]; ring
  apply he.trans_eq
  rw [hpa]
  calc
    _ = (2*C/a)*(H+M)*q^γ-(D/b)*(H+M)*(q*(q^4)^b) := by ring
    _ = _ := by rw [hpb]; ring
end MeasurableSchauder

end

end OAI
