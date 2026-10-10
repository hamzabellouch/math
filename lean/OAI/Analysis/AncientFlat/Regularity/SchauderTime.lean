import OAI.Analysis.AncientFlat.Regularity.SchauderSpace

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BoundedContinuousFunction SchwartzMap
namespace ParabolicSchauder
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma exists_fourth_time_holder_ordered (K : SchwartzMap V ℂ) (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    ∃ B : ℝ, 0≤B ∧ ∀ (f : ℝ → (V →ᵇ ℂ)) (_hf : Continuous f) (H s t : ℝ),
      0≤H → 0 ≤ s → s ≤ t →
      (∀ r ∈ Ioo 0 t, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^α) → ∀ x,
      ‖integratedJet K f t 4 x-integratedJet K f s 4 x‖≤B*H*(t-s)^(α/4) := by
  obtain ⟨C,hC,hb⟩ := exists_jet_bound K 4 (by norm_num) α hα.le hα1.le
  obtain ⟨D,hD,hd⟩ := exists_jet_time_increment K 4 (by norm_num) α hα.le hα1.le
  let a := α/4
  have ha : 0<a := by dsimp [a]; positivity
  have ha1 : a<1 := by dsimp [a]; linarith
  have hpos : 0≤3*C/a := by positivity
  have hneg : D/(a-1)≤0 := div_nonpos_of_nonneg_of_nonpos hD (by linarith)
  refine ⟨3*C/a-D/(a-1),sub_nonneg.mpr (hneg.trans hpos),?_⟩
  intro f hf H s t hH hs hst hh x
  by_cases heq : s=t
  · subst t; simp only [sub_self,norm_zero,Real.zero_rpow (ne_of_gt (by positivity : 0<α/4)),mul_zero,le_refl]
  have he : 0<t-s := sub_pos.mpr (lt_of_le_of_ne hst heq)
  have ht : 0≤t := hs.trans hst
  have hhs : ∀ r ∈ Ioo 0 s, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^α :=
    fun r hr => hh r ⟨hr.1,hr.2.trans_le hst⟩
  have hit := integrable_jet K f hf α H t hα hα1.le hH ht hh 4 le_rfl x
  have his := integrable_jet K f hf α H s hα hα1.le hH hs hhs 4 le_rfl x
  have hist : IntegrableOn (fun r => jet K (t-r) (f r) 4 x) (Ioo 0 s) :=
    hit.mono_set (fun _ hr => ⟨hr.1,hr.2.trans_le hst⟩)
  have htail : ‖∫ r in Ioo s t, jet K (t-r) (f r) 4 x‖≤C*H*(t-s)^a/a := by
    apply norm_integral_reverse_power a (C*H) s t ha hst
    intro r hr
    convert hb (f r) H hH (hh r ⟨hs.trans_lt hr.1,hr.2⟩) (t-r) (sub_pos.mpr hr.2) x using 1
    congr 2; norm_num; dsimp [a]; ring
  have hold := norm_integral_lag_split a (a-1) (2*C*H) (D*H*(t-s)) (t-s) s ha
    (by linarith) (by positivity) (by positivity) he hs
    (fun r => jet K (t-r) (f r) 4 x-jet K (s-r) (f r) 4 x)
    (hist.sub his).aestronglyMeasurable
    (fun r hr _ => by
      have hp : (t-r)^(a-1)≤(s-r)^(a-1) :=
        Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hr.2) (by linarith) (by linarith)
      have h1 := hb (f r) H hH (hhs r hr) (t-r) (sub_pos.mpr (hr.2.trans_le hst)) x
      have h2 := hb (f r) H hH (hhs r hr) (s-r) (sub_pos.mpr hr.2) x
      norm_num only [Nat.cast_ofNat] at h1 h2
      rw [show (α-4)/4=a-1 by dsimp [a]; ring] at h1 h2
      calc
        _ ≤ ‖jet K (t-r) (f r) 4 x‖+‖jet K (s-r) (f r) 4 x‖ := norm_sub_le ..
        _ ≤ C*H*(t-r)^(a-1)+C*H*(s-r)^(a-1) := add_le_add h1 h2
        _ ≤ C*H*(s-r)^(a-1)+C*H*(s-r)^(a-1) := add_le_add (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hH)) le_rfl
        _ = _ := by ring)
    (fun r hr hlong => by
      have hh' := hd (f r) H hH (hhs r hr) (s-r) (t-s) (sub_pos.mpr hr.2) he.le hlong.le x
      rw [show s-r+(t-s)=t-r by ring] at hh'
      convert hh' using 1
      congr 2; norm_num; dsimp [a]; ring)
  have hep : (t-s)*(t-s)^(a-1)=(t-s)^a := by
    calc
      _ = (t-s)^1*(t-s)^(a-1) := by rw [Real.rpow_one]
      _ = (t-s)^(1+(a-1)) := (Real.rpow_add he 1 (a-1)).symm
      _ = _ := by congr 1; ring
  have heq' : integratedJet K f t 4 x-integratedJet K f s 4 x =
      (∫ r in Ioo s t,jet K (t-r) (f r) 4 x)+
      (∫ r in Ioo 0 s,jet K (t-r) (f r) 4 x-jet K (s-r) (f r) 4 x) := by
    unfold integratedJet
    rw [integral_Ioo_split 0 s t hs hst _ hit,integral_sub hist his]
    abel
  rw [heq']
  calc
    _ ≤ ‖∫ r in Ioo s t,jet K (t-r) (f r) 4 x‖+
        ‖∫ r in Ioo 0 s,jet K (t-r) (f r) 4 x-jet K (s-r) (f r) 4 x‖ := norm_add_le ..
    _ ≤ C*H*(t-s)^a/a+(2*C*H*(t-s)^a/a-D*H*(t-s)*(t-s)^(a-1)/(a-1)) := add_le_add htail hold
    _ = (3*C/a-D/(a-1))*H*(t-s)^a := by
      calc
        _ = (3*C/a)*H*(t-s)^a-(D/(a-1))*H*((t-s)*(t-s)^(a-1)) := by ring
        _ = _ := by rw [hep]; ring
lemma exists_fourth_time_holder (K : SchwartzMap V ℂ) (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    ∃ B : ℝ, 0≤B ∧ ∀ (f : ℝ → (V →ᵇ ℂ)) (_hf : Continuous f) (H h : ℝ), 0≤H →
      (∀ r ∈ Icc 0 h, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^α) →
      ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h, ∀ x,
      ‖integratedJet K f t 4 x-integratedJet K f s 4 x‖≤B*H*|t-s|^(α/4) := by
  obtain ⟨B,hB,hb⟩ := exists_fourth_time_holder_ordered K α hα hα1
  refine ⟨B,hB,fun f hf H h hH hh s hs t ht x => ?_⟩
  rcases le_total s t with hst|hts
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact hb f hf H s t hH hs.1 hst (fun r hr => hh r ⟨hr.1.le,hr.2.le.trans ht.2⟩) x
  · rw [norm_sub_rev,abs_of_nonpos (sub_nonpos.mpr hts),neg_sub]
    exact hb f hf H t s hH ht.1 hts (fun r hr => hh r ⟨hr.1.le,hr.2.le.trans hs.2⟩) x
end ParabolicSchauder

end

end OAI
