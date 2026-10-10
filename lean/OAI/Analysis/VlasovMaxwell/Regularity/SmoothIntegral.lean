import Mathlib

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM
universe u v

section SpatialDerivatives
variable {A E W : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma contDiff_iteratedFDeriv_slice {F : A × E → W} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : A × E => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E W).symm.contDiff.comp hF
  | succ n ih =>
    let G : A × E → (E [×n]→L[ℝ] W) := fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2
    change ContDiff ℝ ∞ G at ih
    have he (p : A × E) : fderiv ℝ (fun x => G (p.1,x)) p.2 =
        (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ A E) := by
      have hin : HasFDerivAt (fun x : E => (p.1,x)) (ContinuousLinearMap.inr ℝ A E) p.2 := by
        convert (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1 <;> rfl
      exact ((ih.differentiable (by simp) p).hasFDerivAt.comp p.2 hin).fderiv
    simp only [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    change ContDiff ℝ ∞ (fun p : A × E =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) W).symm (fderiv ℝ (fun x => G (p.1,x)) p.2))
    simp_rw [he]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) W).symm.contDiff.comp
      ((ih.fderiv_right (m:=∞) (by simp)).clm_comp contDiff_const)

end SpatialDerivatives

section CompactFamily
variable {α : Type v} {E : Type u} [TopologicalSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]

def SmoothCompactFamily (F : α → E → W) : Prop :=
  (∀ a, ContDiff ℝ ∞ (F a)) ∧ ∀ n : ℕ,
    Continuous (fun p : E × α => iteratedFDeriv ℝ n (F p.2) p.1)

lemma SmoothCompactFamily.ofJoint {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {G : A × E → W} (hG : ContDiff ℝ ∞ G) {ι : α → A} (hι : Continuous ι) :
    SmoothCompactFamily (fun a x => G (ι a,x)) := by
  refine ⟨fun a => hG.comp (contDiff_const.prodMk contDiff_id),fun n => ?_⟩
  exact (contDiff_iteratedFDeriv_slice hG n).continuous.comp
    ((hι.comp continuous_snd).prodMk continuous_fst)

lemma SmoothCompactFamily.continuous {F : α → E → W} (hF : SmoothCompactFamily F) :
    Continuous (fun p : E × α => F p.2 p.1) := by
  have h := (continuousMultilinearCurryFin0 ℝ E W).continuous.comp (hF.2 0)
  simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,LinearIsometryEquiv.apply_symm_apply] using h

lemma SmoothCompactFamily.derivFamily {F : α → E → W} (hF : SmoothCompactFamily F) :
    SmoothCompactFamily (fun a => fderiv ℝ (F a)) := by
  refine ⟨fun a => (hF.1 a).fderiv_right (m:=∞) (by simp),fun n => ?_⟩
  have he (p : E × α) : iteratedFDeriv ℝ n (fderiv ℝ (F p.2)) p.1 =
      continuousMultilinearCurryRightEquiv' ℝ n E W (iteratedFDeriv ℝ (n+1) (F p.2) p.1) := by
    rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]
  simp_rw [he]
  exact (continuousMultilinearCurryRightEquiv' ℝ n E W).continuous.comp (hF.2 (n+1))

variable [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α]
  [ProperSpace E] [CompleteSpace W]

omit [CompleteSpace W] in
lemma hasFDerivAt_integral_smoothFamily (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → E → W} (hF : SmoothCompactFamily F) (x : E) :
    HasFDerivAt (fun y => ∫ a, F a y ∂μ) (∫ a, fderiv ℝ (F a) x ∂μ) x := by
  have hD := hF.derivFamily.continuous
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod isCompact_univ).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=closedBall x 1) (bound:=fun _ => C) (F':=fun y a => fderiv ℝ (F a) y)
    (closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall (fun y => (hF.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun a y hy => hC _ ⟨(y,a),⟨hy,mem_univ a⟩,rfl⟩)
  · exact integrable_const _
  · exact ae_of_all _ (fun a y _ => ((hF.1 a).differentiable (by simp) y).hasFDerivAt)

lemma contDiff_integral_smoothFamily_nat (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : α → E → W}, SmoothCompactFamily F → ContDiff ℝ n (fun x => ∫ a, F a x ∂μ) := by
  induction n with
  | zero =>
    intro W _ _ _ F hF
    apply contDiff_zero.mpr
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hF.continuous.continuousOn
    intro x a _ ha
    exact (ha (mem_univ a)).elim
  | succ n ih =>
    intro W _ _ _ F hF
    rw [show (↑(n+1) : ℕ∞ω) = ↑n+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_integral_smoothFamily μ hF x).differentiableAt,by simp,?_⟩
    have he : fderiv ℝ (fun x => ∫ a, F a x ∂μ) = (fun x => ∫ a, fderiv ℝ (F a) x ∂μ) := by
      funext x
      exact (hasFDerivAt_integral_smoothFamily μ hF x).fderiv
    rw [he]
    exact ih hF.derivFamily

lemma contDiff_integral_smoothFamily (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → E → W} (hF : SmoothCompactFamily F) : ContDiff ℝ ∞ (fun x => ∫ a, F a x ∂μ) := by
  rw [contDiff_infty]
  exact fun n => contDiff_integral_smoothFamily_nat μ n hF

lemma norm_iteratedFDeriv_integral_le (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : α → E → W}, SmoothCompactFamily F → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) x‖ ≤
        ∫ a, ‖iteratedFDeriv ℝ n (F a) x‖ ∂μ := by
  induction n with
  | zero =>
    intro W _ _ _ F hF x
    simpa only [norm_iteratedFDeriv_zero] using norm_integral_le_integral_norm (fun a => F a x)
  | succ n ih =>
    intro W _ _ _ F hF x
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (fun y => ∫ a, F a y ∂μ) = (fun y => ∫ a, fderiv ℝ (F a) y ∂μ) := by
      funext y
      exact (hasFDerivAt_integral_smoothFamily μ hF y).fderiv
    rw [he]
    simpa only [norm_iteratedFDeriv_fderiv] using ih hF.derivFamily x

end CompactFamily

variable {E W : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

attribute [local instance] Measure.Subtype.measureSpace in
lemma norm_iteratedFDeriv_intervalIntegral_le {F : ℝ × E → W} (hF : ContDiff ℝ ∞ F)
    (n : ℕ) {a b : ℝ} (hab : a≤b) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ r in a..b, F (r,y)) x‖ ≤
      ∫ r in a..b, ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖ := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := norm_iteratedFDeriv_integral_le
    (E:=E) (W:=W) (volume : Measure (Icc a b)) n
    (SmoothCompactFamily.ofJoint (α:=Icc a b) hF continuous_subtype_val) x
  have he (y : E) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  have he' : (∫ r : Icc a b, ‖iteratedFDeriv ℝ n (fun y => F ((r:ℝ),y)) x‖) =
      ∫ r in a..b, ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖ := by
    rw [integral_subtype measurableSet_Icc (fun r => ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖),
      integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]
  simp_rw [he] at hh
  rwa [he'] at hh

attribute [local instance] Measure.Subtype.measureSpace in
lemma contDiff_spatial_intervalIntegral {F : ℝ × E → W} (hF : ContDiff ℝ ∞ F)
    {a b : ℝ} (hab : a≤b) : ContDiff ℝ ∞ (fun y => ∫ r in a..b, F (r,y)) := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := contDiff_integral_smoothFamily (volume : Measure (Icc a b))
    (SmoothCompactFamily.ofJoint (α:=Icc a b) hF continuous_subtype_val)
  have he (y : E) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  simpa only [he] using hh

lemma integral_gronwall_bound {f : ℝ → ℝ} (hf : Continuous f) {a b T : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hn : ∀ t∈Icc 0 T, 0≤f t)
    (hbound : ∀ t∈Icc 0 T, f t≤a+b*∫ r in 0..t, f r) :
    ∀ t∈Icc 0 T, f t≤a*Real.exp (b*t) := by
  let g := fun t => a+b*∫ r in 0..t, f r
  have hg : Continuous g := continuous_const.add
    (continuous_const.mul (intervalIntegral.continuous_primitive hf.intervalIntegrable 0))
  have hnG (t : ℝ) (ht : t∈Icc 0 T) : 0≤g t := by
    exact le_trans (hn t ht) (hbound t ht)
  have hd (t : ℝ) : HasDerivAt g (b*f t) t := by
    convert ((intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_mul b).const_add a using 1
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hg.continuousOn
    (fun t _ => (hd t).hasDerivWithinAt) (a:=0) (b:=T) (δ:=a) (K:=b) (ε:=0)
    (by simp only [g,intervalIntegral.integral_same,mul_zero,add_zero,Real.norm_eq_abs,abs_of_nonneg ha]; exact le_rfl)

    (by
      intro t ht
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hb (hn t ⟨ht.1,ht.2.le⟩)),
        Real.norm_eq_abs,abs_of_nonneg (hnG t ⟨ht.1,ht.2.le⟩),add_zero]
      exact mul_le_mul_of_nonneg_left (hbound t ⟨ht.1,ht.2.le⟩) hb)
  intro t ht
  exact (hbound t ht).trans ((le_abs_self (g t)).trans (by
    simpa only [Real.norm_eq_abs,gronwallBound_ε0,sub_zero] using hh t ht))

end RVM
end

end OAI
