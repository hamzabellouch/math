import Mathlib

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter MeasureTheory
open scoped Topology Interval NNReal

lemma lipschitzOn_sub_le_of_ae_deriv_le {f : ℝ → ℝ} {a b c : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hf : LipschitzOnWith K f (Icc a b))
    (hd : ∀ᵐ x : ℝ, x∈Icc a b → deriv f x ≤ c) :
    f b-f a ≤ c*(b-a) := by
  have ha : AbsolutelyContinuousOnInterval f a b :=
    (by rwa [uIcc_of_le hab] : LipschitzOnWith K f (uIcc a b)).absolutelyContinuousOnInterval
  have H := intervalIntegral.integral_mono_ae_restrict hab ha.intervalIntegrable_deriv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume a b)
    ((ae_restrict_iff' measurableSet_Icc).mpr hd)
  rw [ha.integral_deriv_eq_sub,intervalIntegral.integral_const] at H
  simpa only [smul_eq_mul,mul_comm] using H

lemma lipschitzOn_barrier {f : ℝ → ℝ} {a b c : ℝ} {K : ℝ≥0}
    (_ : a ≤ b) (hf : LipschitzOnWith K f (Icc a b)) (hfa : f a ≤ c)
    (hd : ∀ᵐ x : ℝ, x∈Icc a b → c < f x → deriv f x ≤ 0) :
    ∀ x∈Icc a b, f x ≤ c := by
  intro x hx
  by_contra Hx
  have hcx : c < f x := lt_of_not_ge Hx
  let S : Set ℝ := {r∈Icc a x | f r ≤ c}
  have hxs : Icc a x⊆Icc a b := Icc_subset_Icc_right hx.2
  have hS : IsCompact S :=
    isCompact_Icc.of_isClosed_subset
      (isClosed_Icc.isClosed_le (hf.continuousOn.mono hxs) continuousOn_const)
      (fun _ h => h.1)
  have haS : a∈S := ⟨⟨le_rfl,hx.1⟩,hfa⟩
  obtain ⟨r,hr,hgreat⟩ := hS.exists_isGreatest ⟨a,haS⟩
  have hrx : r < x := lt_of_le_of_ne hr.1.2 (by intro H; subst r; exact (not_le_of_gt hcx) hr.2)
  have hfr : ∀ u∈Icc r x, u≠r → c < f u := by
    intro u hu hur
    by_contra H
    have huS : u∈S := ⟨⟨hr.1.1.trans hu.1,hu.2⟩,le_of_not_gt H⟩
    exact hur (le_antisymm (hgreat huS) hu.1)
  have hsub : Icc r x⊆Icc a b := Icc_subset_Icc hr.1.1 hx.2
  have hd' : ∀ᵐ u : ℝ, u∈Icc r x → deriv f u ≤ 0 := by
    have hneq : ∀ᵐ u : ℝ, u≠r := by rw [ae_iff]; simp
    filter_upwards [hd,hneq] with u hu hur hus
    exact hu (hsub hus) (hfr u hus hur)
  have H := lipschitzOn_sub_le_of_ae_deriv_le hrx.le (hf.mono hsub) hd'
  simp only [zero_mul] at H
  linarith only [H,hr.2,hcx]

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

lemma norm_deficit_advance {q N t D : ℝ} (hq : 0 ≤ q) (hN : 0 ≤ N)
    (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (hD : 0 ≤ D)
    (hgap : q^2 ≤ (1-t)^2*N^2-D) : q*N-(1-t)*N^2 ≤ -D/2 := by
  have ha : 0 ≤ (1-t)*N := mul_nonneg (by linarith only [ht1]) hN
  have hqA : q ≤ (1-t)*N := (sq_le_sq₀ hq ha).mp (by nlinarith only [hgap,hD])
  have hdiff : 0 ≤ (1-t)*N-q := sub_nonneg.mpr hqA
  have hsum : (1-t)*N+q ≤ 2*N := by nlinarith [mul_nonneg ht hN]
  have H := mul_nonneg hdiff (sub_nonneg.mpr hsum)
  nlinarith only [H,hgap]

lemma norm_surplus_advance {q N t D : ℝ} (hq : 0 ≤ q) (hN : 0 ≤ N)
    (_ : 0 ≤ t) (ht1 : t ≤ 1/2) (hD : 0 ≤ D)
    (hgap : q^2 ≤ (1-t)^2*N^2+D) : q*N-(1-t)*N^2 ≤ 2*D := by
  by_cases Hq : q ≤ (1-t)*N
  · have H := mul_le_mul_of_nonneg_right Hq hN
    nlinarith only [H,hD]
  · have hdiff : 0 ≤ q-(1-t)*N := (le_of_not_ge Hq).trans (le_refl _)|> sub_nonneg.mpr
    have hsum : N/2 ≤ (1-t)*N+q := by nlinarith only [ht1,hN,hq,mul_nonneg (sub_nonneg.mpr ht1) hN]
    have H := mul_nonneg hdiff (sub_nonneg.mpr hsum)
    nlinarith only [H,hgap]

end WeakMTWTransport

end

end OAI
