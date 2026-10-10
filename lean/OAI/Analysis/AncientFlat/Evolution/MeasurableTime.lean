import OAI.Analysis.AncientFlat.Evolution.MeasurableSpace

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BoundedContinuousFunction SchwartzMap
namespace MeasurableSchauder
open ParabolicSchauder VariableSchauder
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma exists_fourth_time_holder_ordered (α β L : ℝ) (hα : 0<α) (hαβ : α≤β) (hL : 0≤L) (K : SchwartzMap V ℂ) (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ B : ℝ, 0≤B ∧ ∀ (A : ℝ → V → ℝ), Continuous (Function.uncurry A) →
      (∀ r y, A r y∈Icc α β) → (∀ r x y, ‖A r x-A r y‖≤L*‖x-y‖) →
      ∀ (f : ℝ → (V →ᵇ ℂ)) (_ : StronglyMeasurable f) (H M s t : ℝ),
      0≤H → 0≤M → 0 ≤ s → s ≤ t → t≤1 →
      (∀ r∈Ioo 0 t, ‖f r‖≤M) →
      (∀ r ∈ Ioo 0 t, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^γ) → ∀ x,
      ‖integratedJet K A f t 4 x-integratedJet K A f s 4 x‖≤B*(H+M)*(t-s)^(γ/4) := by
  obtain ⟨C,hC,hb⟩ := exists_jet_bound K 4 (by norm_num) α β γ L hα hγ.le hγ1.le hL
  obtain ⟨D,hD,hd⟩ := exists_jet_time_increment K 4 (by norm_num) α β γ L hα hαβ hγ.le hγ1.le hL
  let a := γ/4
  have ha : 0<a := by dsimp [a]; positivity
  have ha1 : a<1 := by dsimp [a]; linarith
  have hpos : 0≤3*C/a := by positivity
  have hneg : D/(a-1)≤0 := div_nonpos_of_nonneg_of_nonpos hD (by linarith)
  refine ⟨3*C/a-D/(a-1),sub_nonneg.mpr (hneg.trans hpos),?_⟩
  intro A hA hAr hAL f hf H M s t hH hM hs hst ht1 hm hh x
  by_cases heq : s=t
  · subst t; simp only [sub_self,norm_zero,Real.zero_rpow (ne_of_gt (by positivity : 0<γ/4)),mul_zero,le_refl]
  have he : 0<t-s := sub_pos.mpr (lt_of_le_of_ne hst heq)
  have ht : 0≤t := hs.trans hst
  have hhs : ∀ r ∈ Ioo 0 s, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^γ :=
    fun r hr => hh r ⟨hr.1,hr.2.trans_le hst⟩
  have hit := integrable_jet A hA α β L hα hAr hL hAL K f hf γ H M t hγ hγ1.le hH hM ht hm hh 4 le_rfl x
  have his := integrable_jet A hA α β L hα hAr hL hAL K f hf γ H M s hγ hγ1.le hH hM hs (fun r hr => hm r ⟨hr.1,hr.2.trans_le hst⟩) hhs 4 le_rfl x
  have hist : IntegrableOn (fun r => jet K (A r) (t-r) (f r) 4 x) (Ioo 0 s) :=
    hit.mono_set (fun _ hr => ⟨hr.1,hr.2.trans_le hst⟩)
  have htail : ‖∫ r in Ioo s t, jet K (A r) (t-r) (f r) 4 x‖≤C*(H+M)*(t-s)^a/a := by
    apply norm_integral_reverse_power a (C*(H+M)) s t ha hst
    intro r hr
    convert hb (A r) (hA.comp (continuous_const.prodMk continuous_id)) (hAr r) (hAL r) (f r) H M hH hM (hm r ⟨hs.trans_lt hr.1,hr.2⟩) (hh r ⟨hs.trans_lt hr.1,hr.2⟩) (t-r) (sub_pos.mpr hr.2) (by linarith [hr.1]) x using 1
    congr 2; norm_num; dsimp [a]; ring
  have hold := norm_integral_lag_split a (a-1) (2*C*(H+M)) (D*(H+M)*(t-s)) (t-s) s ha
    (by linarith) (by positivity) (by positivity) he hs
    (fun r => jet K (A r) (t-r) (f r) 4 x-jet K (A r) (s-r) (f r) 4 x)
    (hist.sub his).aestronglyMeasurable
    (fun r hr _ => by
      have hp : (t-r)^(a-1)≤(s-r)^(a-1) :=
        Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hr.2) (by linarith) (by linarith)
      have h1 := hb (A r) (hA.comp (continuous_const.prodMk continuous_id)) (hAr r) (hAL r) (f r) H M hH hM (hm r ⟨hr.1,hr.2.trans_le hst⟩) (hhs r hr) (t-r) (sub_pos.mpr (hr.2.trans_le hst)) (by linarith [hr.1]) x
      have h2 := hb (A r) (hA.comp (continuous_const.prodMk continuous_id)) (hAr r) (hAL r) (f r) H M hH hM (hm r ⟨hr.1,hr.2.trans_le hst⟩) (hhs r hr) (s-r) (sub_pos.mpr hr.2) (by linarith [hr.1]) x
      norm_num only [Nat.cast_ofNat] at h1 h2
      rw [show (γ-4)/4=a-1 by dsimp [a]; ring] at h1 h2
      calc
        _ ≤ ‖jet K (A r) (t-r) (f r) 4 x‖+‖jet K (A r) (s-r) (f r) 4 x‖ := norm_sub_le ..
        _ ≤ C*(H+M)*(t-r)^(a-1)+C*(H+M)*(s-r)^(a-1) := add_le_add h1 h2
        _ ≤ C*(H+M)*(s-r)^(a-1)+C*(H+M)*(s-r)^(a-1) := add_le_add (mul_le_mul_of_nonneg_left hp (mul_nonneg hC (add_nonneg hH hM))) le_rfl
        _ = _ := by ring)
    (fun r hr hlong => by
      have hh' := hd (A r) (hA.comp (continuous_const.prodMk continuous_id)) (hAr r) (hAL r) (f r) H M hH hM (hm r ⟨hr.1,hr.2.trans_le hst⟩) (hhs r hr) (s-r) (t-s) (sub_pos.mpr hr.2) (by linarith [hr.1]) he.le hlong.le x
      rw [show s-r+(t-s)=t-r by ring] at hh'
      convert hh' using 1
      congr 2; norm_num; dsimp [a]; ring)
  have hep : (t-s)*(t-s)^(a-1)=(t-s)^a := by
    calc
      _ = (t-s)^1*(t-s)^(a-1) := by rw [Real.rpow_one]
      _ = (t-s)^(1+(a-1)) := (Real.rpow_add he 1 (a-1)).symm
      _ = _ := by congr 1; ring
  have heq' : integratedJet K A f t 4 x-integratedJet K A f s 4 x =
      (∫ r in Ioo s t,jet K (A r) (t-r) (f r) 4 x)+
      (∫ r in Ioo 0 s,jet K (A r) (t-r) (f r) 4 x-jet K (A r) (s-r) (f r) 4 x) := by
    unfold integratedJet
    rw [integral_Ioo_split 0 s t hs hst _ hit,integral_sub hist his]
    abel
  rw [heq']
  calc
    _ ≤ ‖∫ r in Ioo s t,jet K (A r) (t-r) (f r) 4 x‖+
        ‖∫ r in Ioo 0 s,jet K (A r) (t-r) (f r) 4 x-jet K (A r) (s-r) (f r) 4 x‖ := norm_add_le ..
    _ ≤ C*(H+M)*(t-s)^a/a+(2*C*(H+M)*(t-s)^a/a-D*(H+M)*(t-s)*(t-s)^(a-1)/(a-1)) := add_le_add htail hold
    _ = (3*C/a-D/(a-1))*(H+M)*(t-s)^a := by
      calc
        _ = (3*C/a)*(H+M)*(t-s)^a-(D/(a-1))*(H+M)*((t-s)*(t-s)^(a-1)) := by ring
        _ = _ := by rw [hep]; ring
lemma exists_fourth_time_holder (α β L : ℝ) (hα : 0<α) (hαβ : α≤β) (hL : 0≤L)
    (K : SchwartzMap V ℂ) (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ B : ℝ, 0≤B ∧ ∀ (A : ℝ → V → ℝ), Continuous (Function.uncurry A) →
      (∀ r y, A r y∈Icc α β) → (∀ r x y, ‖A r x-A r y‖≤L*‖x-y‖) →
      ∀ (f : ℝ → (V →ᵇ ℂ)) (_ : StronglyMeasurable f) (H M h : ℝ), 0≤H → 0≤M → h≤1 →
      (∀ r∈Icc 0 h, ‖f r‖≤M) →
      (∀ r ∈ Icc 0 h, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^γ) →
      ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h, ∀ x,
      ‖integratedJet K A f t 4 x-integratedJet K A f s 4 x‖≤B*(H+M)*|t-s|^(γ/4) := by
  obtain ⟨B,hB,hb⟩ := exists_fourth_time_holder_ordered α β L hα hαβ hL K γ hγ hγ1
  refine ⟨B,hB,fun A hA hAr hAL f hf H M h hH hM hh1 hm hh s hs t ht x => ?_⟩
  rcases le_total s t with hst|hts
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact hb A hA hAr hAL f hf H M s t hH hM hs.1 hst (ht.2.trans hh1)
      (fun r hr => hm r ⟨hr.1.le,hr.2.le.trans ht.2⟩)
      (fun r hr => hh r ⟨hr.1.le,hr.2.le.trans ht.2⟩) x
  · rw [norm_sub_rev,abs_of_nonpos (sub_nonpos.mpr hts),neg_sub]
    exact hb A hA hAr hAL f hf H M t s hH hM ht.1 hts (hs.2.trans hh1)
      (fun r hr => hm r ⟨hr.1.le,hr.2.le.trans hs.2⟩)
      (fun r hr => hh r ⟨hr.1.le,hr.2.le.trans hs.2⟩) x
end MeasurableSchauder

end

end OAI
