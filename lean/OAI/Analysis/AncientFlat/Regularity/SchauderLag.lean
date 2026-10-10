import Mathlib

namespace OAI
noncomputable section
open Set Filter MeasureTheory
namespace ParabolicSchauder

def lagMajorant (a b p q δ : ℝ) (r : ℝ) : ℝ :=
  if r ≤ δ then p*r^(a-1) else q*r^(b-1)
lemma integral_short_power (a δ : ℝ) (ha : 0<a) (hδ : 0≤δ) :
    ∫ r in Ioc 0 δ, r^(a-1) = δ^a/a := by
  rw [← intervalIntegral.integral_of_le hδ,integral_rpow (Or.inl (by linarith : -1<a-1))]
  simp only [sub_add_cancel,Real.zero_rpow ha.ne',sub_zero]
lemma integrable_short_power (a δ : ℝ) (ha : 0<a) (hδ : 0≤δ) :
    IntegrableOn (fun r : ℝ => r^(a-1)) (Ioc 0 δ) := by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<a-1))
lemma integrable_lagMajorant (a b p q δ : ℝ) (ha : 0<a) (hb : b<0) (hδ : 0<δ) :
    IntegrableOn (lagMajorant a b p q δ) (Ioi 0) := by
  have hs : IntegrableOn (lagMajorant a b p q δ) (Ioc 0 δ) :=
    IntegrableOn.congr_fun ((integrable_short_power a δ ha hδ.le).const_mul p)
      (fun r hr => by simp [lagMajorant,hr.2]) measurableSet_Ioc
  have hl : IntegrableOn (lagMajorant a b p q δ) (Ioi δ) :=
    IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt (by linarith : b-1 < -1) hδ).const_mul q)
      (fun r hr => by simp [lagMajorant,not_le.mpr (show δ<r from hr)]) measurableSet_Ioi
  have he : Ioc 0 δ ∪ Ioi δ = Ioi (0:ℝ) := by
    ext r
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (⟨h,_⟩|h)
      · exact h
      · exact hδ.trans h
    · intro h
      rcases le_or_gt r δ with hr|hr
      · exact Or.inl ⟨h,hr⟩
      · exact Or.inr hr
  rw [← he]
  exact hs.union hl
lemma integral_lagMajorant (a b p q δ : ℝ) (ha : 0<a) (hb : b<0) (hδ : 0<δ) :
    ∫ r in Ioi 0, lagMajorant a b p q δ r = p*δ^a/a-q*δ^b/b := by
  have hi := integrable_lagMajorant a b p q δ ha hb hδ
  have hs : Ioc 0 δ ⊆ Ioi (0:ℝ) := fun _ h => h.1
  have hl : Ioi δ ⊆ Ioi (0:ℝ) := fun _ h => hδ.trans h
  have he : Ioc 0 δ ∪ Ioi δ = Ioi (0:ℝ) := by
    ext r
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (⟨h,_⟩|h)
      · exact h
      · exact hδ.trans h
    · intro h
      rcases le_or_gt r δ with hr|hr
      · exact Or.inl ⟨h,hr⟩
      · exact Or.inr hr
  rw [← he,setIntegral_union (by exact disjoint_left.mpr (fun r h k => (not_lt_of_ge h.2 k))) measurableSet_Ioi (hi.mono_set hs) (hi.mono_set hl)]
  have h1 : ∫ r in Ioc 0 δ, lagMajorant a b p q δ r = p*(δ^a/a) := by
    rw [setIntegral_congr_fun (g := fun r => p*r^(a-1)) measurableSet_Ioc (fun r hr => by simp [lagMajorant,hr.2]),integral_const_mul,integral_short_power a δ ha hδ.le]
  have h2 : ∫ r in Ioi δ, lagMajorant a b p q δ r = q*(-δ^b/b) := by
    rw [setIntegral_congr_fun (g := fun r => q*r^(b-1)) measurableSet_Ioi (fun r hr => by simp [lagMajorant,not_le.mpr (show δ<r from hr)]),integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : b-1 < -1) hδ]
    simp only [sub_add_cancel]
  rw [h1,h2]
  ring
lemma lagMajorant_nonneg (a b p q δ r : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r) :
    0≤lagMajorant a b p q δ r := by
  unfold lagMajorant
  split <;> positivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma norm_integral_lag_split (a b p q δ t : ℝ) (ha : 0<a) (hb : b<0)
    (hp : 0≤p) (hq : 0≤q) (hδ : 0<δ) (ht : 0≤t) (f : ℝ → E)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo 0 t)))
    (hshort : ∀ r ∈ Ioo 0 t, t-r ≤ δ → ‖f r‖≤p*(t-r)^(a-1))
    (hlong : ∀ r ∈ Ioo 0 t, δ < t-r → ‖f r‖≤q*(t-r)^(b-1)) :
    ‖∫ r in Ioo 0 t, f r‖≤p*δ^a/a-q*δ^b/b := by
  let g := lagMajorant a b p q δ
  have hg := integrable_lagMajorant a b p q δ ha hb hδ
  have hg0 : IntegrableOn g (Ioc 0 t) := hg.mono_set (fun _ h => h.1)
  have hgi : IntervalIntegrable g volume 0 t := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hg0
  have hgsub : IntervalIntegrable (fun r => g (t-r)) volume 0 t := by
    simpa only [sub_self,sub_zero] using (hgi.comp_sub_left t).symm
  have hgsub' : IntegrableOn (fun r => g (t-r)) (Ioo 0 t) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hgsub).mono_set Ioo_subset_Ioc_self
  have hbd : ∀ r ∈ Ioo 0 t, ‖f r‖≤g (t-r) := by
    intro r hr
    by_cases hh : t-r≤δ
    · simpa only [g,lagMajorant,ite_eq_left hh] using hshort r hr hh
    · simpa only [g,lagMajorant,ite_eq_right hh] using hlong r hr (lt_of_not_ge hh)
  have hfi : IntegrableOn f (Ioo 0 t) := hgsub'.mono' hf (ae_restrict_of_forall_mem measurableSet_Ioo hbd)
  calc
    _ ≤ ∫ r in Ioo 0 t, g (t-r) :=
      norm_integral_le_of_norm_le hgsub' (ae_restrict_of_forall_mem measurableSet_Ioo hbd)
    _ = ∫ r in Ioc 0 t, g r := by
      rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le ht,
        intervalIntegral.integral_comp_sub_left,sub_self,sub_zero,intervalIntegral.integral_of_le ht]
    _ ≤ ∫ r in Ioi 0, g r := setIntegral_mono_set hg
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => lagMajorant_nonneg a b p q δ r hp hq hr.le))
      (by filter_upwards with r hr; exact hr.1)
    _ = _ := integral_lagMajorant a b p q δ ha hb hδ
lemma integrable_reverse_power (a u v : ℝ) (ha : 0<a) (huv : u≤v) :
    IntegrableOn (fun r => (v-r)^(a-1)) (Ioo u v) := by
  have hi : IntervalIntegrable (fun r : ℝ => r^(a-1)) volume 0 (v-u) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<a-1)
  have hi' := hi.comp_sub_left v
  rw [sub_zero,sub_sub_cancel] at hi'
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mp hi'.symm).mono_set Ioo_subset_Ioc_self
lemma integral_reverse_power (a u v : ℝ) (ha : 0<a) (huv : u≤v) :
    ∫ r in Ioo u v, (v-r)^(a-1) = (v-u)^a/a := by
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le huv,
    intervalIntegral.integral_comp_sub_left (f := fun r : ℝ => r^(a-1)) v,sub_self,intervalIntegral.integral_of_le (sub_nonneg.mpr huv)]
  exact integral_short_power a (v-u) ha (sub_nonneg.mpr huv)
omit [CompleteSpace E] in
lemma norm_integral_reverse_power (a M u v : ℝ) (ha : 0<a) (huv : u≤v)
    (f : ℝ → E) (hb : ∀ r ∈ Ioo u v, ‖f r‖≤M*(v-r)^(a-1)) :
    ‖∫ r in Ioo u v, f r‖≤M*(v-u)^a/a := by
  calc
    _ ≤ ∫ r in Ioo u v, M*(v-r)^(a-1) := norm_integral_le_of_norm_le
      ((integrable_reverse_power a u v ha huv).const_mul M)
      (ae_restrict_of_forall_mem measurableSet_Ioo hb)
    _ = _ := by rw [integral_const_mul,integral_reverse_power a u v ha huv]; ring
omit [CompleteSpace E] in
lemma integral_Ioo_split (u s t : ℝ) (hus : u ≤ s) (hst : s ≤ t) (f : ℝ → E)
    (hf : IntegrableOn f (Ioo u t)) :
    (∫ r in Ioo u t,f r) = (∫ r in Ioo u s,f r)+(∫ r in Ioo s t,f r) := by
  have h1 : IntervalIntegrable f volume u s :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hus).mpr (hf.mono_set (fun _ h => ⟨h.1,h.2.trans_le hst⟩))
  have h2 : IntervalIntegrable f volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hst).mpr (hf.mono_set (fun _ h => ⟨hus.trans_lt h.1,h.2⟩))
  simp_rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le (hus.trans hst),← intervalIntegral.integral_of_le hus,
    ← intervalIntegral.integral_of_le hst]
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
end ParabolicSchauder

end

end OAI
