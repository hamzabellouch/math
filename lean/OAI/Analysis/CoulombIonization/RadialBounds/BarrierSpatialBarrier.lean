import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierNonlinearBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma spatial_source_locallyIntegrable {g χ u : TFSpace → ℝ} {F : TFSpace → ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2)) (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*F x (u x)) := by
  have hχl : LocallyIntegrable χ :=
    (memLp_top_of_bound hχ.aestronglyMeasurable 1 (Eventually.of_forall hbχ)).locallyIntegrable le_top
  exact hg.add (LocallyIntegrable.mul_continuous (hF.comp (continuous_id.prodMk hu)) hχl)

theorem weak_maximum_spatial {U : Set TFSpace} (hU : IsOpen U)
    {u v g χ : TFSpace → ℝ} {F : TFSpace → ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hg : LocallyIntegrable g)
    (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1) (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2))
    (hwu : WeakLaplacianLowerOn U u (fun x => g x+χ x*F x (u x)))
    (hwv : WeakLaplacianLowerOn U v (fun x => g x+χ x*F x (v x))) :
    WeakLaplacianLowerOn U (fun x => max (u x) (v x))
      (fun x => g x+χ x*F x (max (u x) (v x))) := by
  let w : TFSpace → ℝ := fun x => max (u x) (v x)
  have hwc : Continuous w := hu.max hv
  have hgu := spatial_source_locallyIntegrable hg hχ hbχ hF hu
  have hgv := spatial_source_locallyIntegrable hg hχ hbχ hF hv
  have hgw := spatial_source_locallyIntegrable hg hχ hbχ hF hwc
  apply weak_lower_of_constant_errors hgw
  intro ε hε
  have hge : LocallyIntegrable (fun x => (g x+χ x*F x (w x))-ε) :=
    hgw.sub (locallyIntegrable_const ε)
  apply weak_lower_local hwc.locallyIntegrable hge
  intro x hx
  by_cases heq : u x = v x
  · let V := U ∩ {y | ‖F y (u y)-F y (v y)‖ < ε}
    have hVo : IsOpen V := hU.inter (isOpen_lt ((hF.comp (continuous_id.prodMk hu)).sub (hF.comp (continuous_id.prodMk hv))).norm continuous_const)
    have hxV : x ∈ V := ⟨hx,by simp only [mem_ofPred_eq,heq,sub_self,norm_zero]; exact hε⟩
    have hcu : WeakLaplacianLowerOn V u (fun x => (g x+χ x*F x (w x))-ε) := by
      apply (hwu.mono_set inter_subset_left).source_mono hgu hge
      intro y hy
      have he := weighted_max_reaction_le (hbχ y) hε.le hy.2.le
      change χ y*F y (w y)-ε ≤ χ y*F y (u y) at he
      linarith
    have hcv : WeakLaplacianLowerOn V v (fun x => (g x+χ x*F x (w x))-ε) := by
      apply (hwv.mono_set inter_subset_left).source_mono hgv hge
      intro y hy
      have he := weighted_max_reaction_le (F := F y) (a := v y) (b := u y)
        (hbχ y) hε.le (by rw [norm_sub_rev]; exact hy.2.le)
      rw [max_comm] at he
      change χ y*F y (w y)-ε ≤ χ y*F y (v y) at he
      linarith
    exact ⟨V,hVo,hxV,weak_maximum_common_locallyIntegrable_source hVo hu hv hge hcu hcv⟩
  · rcases lt_or_gt_of_ne heq with huv | hvu
    · let V := U ∩ {y | u y < v y}
      have hVo : IsOpen V := hU.inter (isOpen_lt hu hv)
      have hvw : ∀ y ∈ V, v y = w y := fun y hy => (max_eq_right hy.2.le).symm
      have he : WeakLaplacianLowerOn V v (fun x => (g x+χ x*F x (w x))-ε) := by
        apply (hwv.mono_set inter_subset_left).source_mono hgv hge
        intro y hy
        rw [←hvw y hy]
        linarith
      exact ⟨V,hVo,⟨hx,huv⟩,he.congr_field hvw⟩
    · let V := U ∩ {y | v y < u y}
      have hVo : IsOpen V := hU.inter (isOpen_lt hv hu)
      have huw : ∀ y ∈ V, u y = w y := fun y hy => (max_eq_left hy.2.le).symm
      have he : WeakLaplacianLowerOn V u (fun x => (g x+χ x*F x (w x))-ε) := by
        apply (hwu.mono_set inter_subset_left).source_mono hgu hge
        intro y hy
        rw [←huw y hy]
        linarith
      exact ⟨V,hVo,⟨hx,hvu⟩,he.congr_field huw⟩

theorem weak_finset_maximum_spatial {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {U : Set TFSpace} (hU : IsOpen U) (u : ι → TFSpace → ℝ)
    (hu : ∀ i ∈ s, Continuous (u i)) {g χ : TFSpace → ℝ} {F : TFSpace → ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2))
    (hw : ∀ i ∈ s, WeakLaplacianLowerOn U (u i) (fun x => g x+χ x*F x (u i x))) :
    WeakLaplacianLowerOn U (fun x => s.sup' hs (fun i => u i x))
      (fun x => g x+χ x*F x (s.sup' hs (fun i => u i x))) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s hi ih =>
    by_cases hs' : s.Nonempty
    · have hu' : ∀ j ∈ s, Continuous (u j) := fun j hj => hu j (Finset.mem_insert_of_mem hj)
      have hw' : ∀ j ∈ s, WeakLaplacianLowerOn U (u j) (fun x => g x+χ x*F x (u j x)) :=
        fun j hj => hw j (Finset.mem_insert_of_mem hj)
      have hh := weak_maximum_spatial hU (hu i (Finset.mem_insert_self _ _))
        (Continuous.finset_sup'_apply hs' hu') hg hχ hbχ hF
        (hw i (Finset.mem_insert_self _ _)) (ih hs' hu' hw')
      simpa only [Finset.sup'_insert hs'] using hh
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      simpa only [Finset.insert_empty,Finset.sup'_singleton] using hw i (Finset.mem_singleton_self i)

end CoulombBarrier

end

end OAI
