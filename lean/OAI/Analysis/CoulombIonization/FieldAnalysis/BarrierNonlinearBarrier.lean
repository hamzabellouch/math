import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierWeakMaxGeneralBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma WeakLaplacianLowerOn.mono_set {U V : Set TFSpace} {u h : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hVU : V ⊆ U) : WeakLaplacianLowerOn V u h :=
  fun φ hφ hc hs hn => hw φ hφ hc (hs.trans hVU) hn

lemma WeakLaplacianLowerOn.congr_field {U : Set TFSpace} {u v h : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (he : ∀ x ∈ U, u x = v x) :
    WeakLaplacianLowerOn U v h := by
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ x, u x*Δ φ x := hw φ hφ hc hs hn
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : Δ φ x = 0
      · rw [hx,mul_zero,mul_zero]
      · rw [he x (hs (tfLaplacian_support hφ hx))])

lemma WeakLaplacianLowerOn.source_mono_ae {U : Set TFSpace} {u h h' : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hh : LocallyIntegrable h)
    (hh' : LocallyIntegrable h') (hle : ∀ᵐ x, x ∈ U → h' x ≤ h x) :
    WeakLaplacianLowerOn U u h' := by
  intro φ hφ hc hs hn
  apply le_trans _ (hw φ hφ hc hs hn)
  apply integral_mono_ae (locallyIntegrable_mul_test hh' hφ.continuous hc)
    (locallyIntegrable_mul_test hh hφ.continuous hc)
  filter_upwards [hle] with x hx
  by_cases hφx : φ x = 0
  · simp only [hφx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hx (hs (subset_tsupport φ hφx))) (hn x)

lemma WeakLaplacianLowerOn.source_mono {U : Set TFSpace} {u h h' : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hh : LocallyIntegrable h)
    (hh' : LocallyIntegrable h') (hle : ∀ x ∈ U, h' x ≤ h x) :
    WeakLaplacianLowerOn U u h' := hw.source_mono_ae hh hh' (Eventually.of_forall hle)

lemma weak_lower_local {U : Set TFSpace} {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) (hh : LocallyIntegrable h)
    (hw : ∀ x ∈ U, ∃ V : Set TFSpace, IsOpen V ∧ x ∈ V ∧ WeakLaplacianLowerOn V u h) :
    WeakLaplacianLowerOn U u h := by
  choose V hV hxV hW using fun x : U => hw x x.property
  apply (weak_lower_open_cover hV hu hh hW).mono_set
  intro x hx
  exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩

lemma weak_lower_of_constant_errors {U : Set TFSpace} {u h : TFSpace → ℝ}
    (hh : LocallyIntegrable h)
    (hw : ∀ ε > 0, WeakLaplacianLowerOn U u (fun x => h x-ε)) :
    WeakLaplacianLowerOn U u h := by
  intro φ hφ hc hs hn
  have hi := locallyIntegrable_mul_test hh hφ.continuous hc
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
  have he (ε : ℝ) (hε : 0 < ε) :
      (∫ x, h x*φ x)-ε*(∫ x, φ x) ≤ ∫ x, u x*Δ φ x := by
    have ht := hw ε hε φ hφ hc hs hn
    simp_rw [sub_mul] at ht
    rwa [integral_sub hi (hφi.const_mul ε),integral_const_mul] at ht
  have ht := (tendsto_const_nhds (x := ∫ x, h x*φ x)).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (∫ x, φ x))
  have hb := le_of_tendsto ht (Eventually.of_forall fun n : ℕ =>
    he (1/((n:ℝ)+1)) (by positivity))
  simpa only [zero_mul,sub_zero] using hb

lemma semilinear_source_locallyIntegrable {g χ u : TFSpace → ℝ} {F : ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous F) (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*F (u x)) := by
  have hχl : LocallyIntegrable χ :=
    (memLp_top_of_bound hχ.aestronglyMeasurable 1 (Eventually.of_forall hbχ)).locallyIntegrable le_top
  exact hg.add (LocallyIntegrable.mul_continuous (hF.comp hu) hχl)

lemma weighted_max_reaction_le {F : ℝ → ℝ} {a b χ ε : ℝ}
    (hχ : ‖χ‖ ≤ 1) (hε : 0 ≤ ε) (hF : ‖F a-F b‖ ≤ ε) :
    χ*F (max a b)-ε ≤ χ*F a := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    have hb : χ*(F b-F a) ≤ ε := by
      calc
        _ ≤ ‖χ*(F b-F a)‖ := le_abs_self _
        _ = ‖χ‖*‖F a-F b‖ := by rw [norm_mul,norm_sub_rev]
        _ ≤ 1*ε := mul_le_mul hχ hF (norm_nonneg _) (by norm_num)
        _ = ε := one_mul _
    nlinarith
  · rw [max_eq_left hba]
    linarith

theorem weak_maximum_semilinear {U : Set TFSpace} (hU : IsOpen U)
    {u v g χ : TFSpace → ℝ} {F : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hg : LocallyIntegrable g)
    (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1) (hF : Continuous F)
    (hwu : WeakLaplacianLowerOn U u (fun x => g x+χ x*F (u x)))
    (hwv : WeakLaplacianLowerOn U v (fun x => g x+χ x*F (v x))) :
    WeakLaplacianLowerOn U (fun x => max (u x) (v x))
      (fun x => g x+χ x*F (max (u x) (v x))) := by
  let w : TFSpace → ℝ := fun x => max (u x) (v x)
  have hwc : Continuous w := hu.max hv
  have hgu := semilinear_source_locallyIntegrable hg hχ hbχ hF hu
  have hgv := semilinear_source_locallyIntegrable hg hχ hbχ hF hv
  have hgw := semilinear_source_locallyIntegrable hg hχ hbχ hF hwc
  apply weak_lower_of_constant_errors hgw
  intro ε hε
  have hge : LocallyIntegrable (fun x => (g x+χ x*F (w x))-ε) :=
    hgw.sub (locallyIntegrable_const ε)
  apply weak_lower_local hwc.locallyIntegrable hge
  intro x hx
  by_cases heq : u x = v x
  · let V := U ∩ {y | ‖F (u y)-F (v y)‖ < ε}
    have hVo : IsOpen V := hU.inter (isOpen_lt ((hF.comp hu).sub (hF.comp hv)).norm continuous_const)
    have hxV : x ∈ V := ⟨hx,by simp only [mem_ofPred_eq,heq,sub_self,norm_zero]; exact hε⟩
    have hcu : WeakLaplacianLowerOn V u (fun x => (g x+χ x*F (w x))-ε) := by
      apply (hwu.mono_set inter_subset_left).source_mono hgu hge
      intro y hy
      have he := weighted_max_reaction_le (hbχ y) hε.le hy.2.le
      change χ y*F (w y)-ε ≤ χ y*F (u y) at he
      linarith
    have hcv : WeakLaplacianLowerOn V v (fun x => (g x+χ x*F (w x))-ε) := by
      apply (hwv.mono_set inter_subset_left).source_mono hgv hge
      intro y hy
      have he := weighted_max_reaction_le (F := F) (a := v y) (b := u y)
        (hbχ y) hε.le (by rw [norm_sub_rev]; exact hy.2.le)
      rw [max_comm] at he
      change χ y*F (w y)-ε ≤ χ y*F (v y) at he
      linarith
    exact ⟨V,hVo,hxV,weak_maximum_common_locallyIntegrable_source hVo hu hv hge hcu hcv⟩
  · rcases lt_or_gt_of_ne heq with huv | hvu
    · let V := U ∩ {y | u y < v y}
      have hVo : IsOpen V := hU.inter (isOpen_lt hu hv)
      have hvw : ∀ y ∈ V, v y = w y := fun y hy => (max_eq_right hy.2.le).symm
      have he : WeakLaplacianLowerOn V v (fun x => (g x+χ x*F (w x))-ε) := by
        apply (hwv.mono_set inter_subset_left).source_mono hgv hge
        intro y hy
        rw [←hvw y hy]
        linarith
      exact ⟨V,hVo,⟨hx,huv⟩,he.congr_field hvw⟩
    · let V := U ∩ {y | v y < u y}
      have hVo : IsOpen V := hU.inter (isOpen_lt hv hu)
      have huw : ∀ y ∈ V, u y = w y := fun y hy => (max_eq_left hy.2.le).symm
      have he : WeakLaplacianLowerOn V u (fun x => (g x+χ x*F (w x))-ε) := by
        apply (hwu.mono_set inter_subset_left).source_mono hgu hge
        intro y hy
        rw [←huw y hy]
        linarith
      exact ⟨V,hVo,⟨hx,hvu⟩,he.congr_field huw⟩

end CoulombBarrier

end

end OAI
