import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.FormGeneratorSymmetric
import OAI.Geometry.WeakHessian.HeatFlow.CheegerResolventDavies
import OAI.Geometry.WeakHessian.Sobolev.Integral
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatContinuous
import OAI.Geometry.WeakHessian.Measure.DecayCutoffLp
import OAI.Geometry.WeakHessian.LocalBounds.EnergyIdentification

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile216
noncomputable section
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma identified_cheegerHeat_davies_generator
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (_origin : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ‖expMulLp hV.continuous.aestronglyMeasurable hB (cheegerHeat h t u)‖^2 ≤
      ‖expMulLp hV.continuous.aestronglyMeasurable hB u‖^2*Real.exp (2*(L:ℝ)^2*t) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let T := expMulLp hV.continuous.aestronglyMeasurable hB
  let f : ℝ → ℝ := fun s => ‖T (cheegerHeat h s u)‖^2
  let f' : ℝ → ℝ := fun s => 2*⟪T (cheegerHeat h s u),T (cheegerHeat h s A)⟫_ℝ
  have hder (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt f (f' s) (Ici s) s := by
    have HS := (cheeger_closedQuadraticEnergy h).heat_deriv_form_right m (cheeger_domain_dense h) hu hs
    change HasDerivWithinAt (fun r : ℝ => cheegerHeat h r u) (cheegerHeat h s A) (Ici s) s at HS
    exact (T.hasFDerivAt.comp_hasDerivWithinAt s HS).norm_sq
  have hbound (s : ℝ) (_hs : 0 ≤ s) : f' s ≤ 2*(L:ℝ)^2*f s := by
    have hG := identified_isLaplacian_of_formGenerator hfinite hID h (cheegerHeat h s u)
      (cheegerHeat h s A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu s)
    have HD := hG.davies_form hfinite (hpar) hV hB
    dsimp only [f',f,T]
    rw [expMulLp_inner,expMulLp_norm_sq]
    linarith
  have hcont : ContinuousOn f (Icc 0 t) := by
    have H := (cheeger_closedQuadraticEnergy h).heat_lipschitz_on_generator m hu
    change LipschitzOnWith _ (fun s : ℝ => cheegerHeat h s u) (Ici 0) at H
    exact (T.continuous.comp_continuousOn (H.continuousOn.mono Icc_subset_Ici_self)).norm.pow 2
  have H := le_gronwallBound_of_liminf_deriv_right_le (f' := f') (K := 2*(L:ℝ)^2) (ε := 0) hcont
    (fun s hs r hr => (hder s hs.1).liminf_right_slope_le hr)
    (show f 0 ≤ ‖T u‖^2 by simp [f,T,cheegerHeat_zero])
    (fun s hs => by simpa only [add_zero] using hbound s hs.1) t (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩)
  simpa only [gronwallBound_ε0,sub_zero,f,T] using H

lemma identified_cheegerResolvent_davies
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (_origin : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) (hsmall : t*(L:ℝ)^2 < 1) :
    ‖expMulLp hV.continuous.aestronglyMeasurable hB
        (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u)‖ ≤
      ‖expMulLp hV.continuous.aestronglyMeasurable hB u‖/(1-t*(L:ℝ)^2) := by
  let Q := cheeger_closedQuadraticEnergy h
  let v := (Q.scale ht).resolvent u
  let A := t⁻¹ • (v-u)
  let T := expMulLp hV.continuous.aestronglyMeasurable hB
  have hu : Q.IsFormGenerator v A := (Q.scaled_resolvent_iff ht u v).mp rfl
  have hG := identified_isLaplacian_of_formGenerator hfinite hID h v A hu
  have HD := hG.davies_form hfinite (hpar) hV hB
  rw [← expMulLp_inner hV.continuous.aestronglyMeasurable hB v A,
    ← expMulLp_norm_sq hV.continuous.aestronglyMeasurable hB v] at HD
  change ⟪T v,T A⟫_ℝ ≤ (L:ℝ)^2*‖T v‖^2 at HD
  have he : ⟪T v,T A⟫_ℝ = t⁻¹*(‖T v‖^2-⟪T v,T u⟫_ℝ) := by
    simp only [A,map_smul,map_sub,real_inner_smul_right,inner_sub_right,real_inner_self_eq_norm_sq]
  rw [he] at HD
  have HC := real_inner_le_norm (T v) (T u)
  have HI := mul_le_mul_of_nonneg_left HD ht.le
  rw [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] at HI
  change ‖T v‖ ≤ ‖T u‖/(1-t*(L:ℝ)^2)
  rw [le_div_iff₀ (sub_pos.mpr hsmall)]
  by_cases hv : ‖T v‖ = 0
  · simp only [hv,zero_mul]; positivity
  · have hvp : 0 < ‖T v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    nlinarith

lemma identified_cheegerResolvent_weighted
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (hsmall : t*(L:ℝ)^2 < 1) :
    MemLp (fun x => (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x*
      Real.exp (V x)) 2 m := by
  apply (memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable _ (B :=
    (‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2))^2) ?_).1
  intro n
  have HD := identified_cheegerResolvent_davies hID hpar hfinite o h u ht (hV.min_const (n:ℝ))
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) hsmall
  have HU := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
  have H := HD.trans (div_le_div_of_nonneg_right HU (sub_pos.mpr hsmall).le)
  exact pow_le_pow_left₀ (norm_nonneg _) H 2

lemma identified_cheegerResolvent_weighted_norm
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (hsmall : t*(L:ℝ)^2 < 1) :
    ‖(identified_cheegerResolvent_weighted hID hpar hfinite o h u ht hV hU hsmall).toLp
      (fun x => (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x*
      Real.exp (V x))‖ ≤ ‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2) := by
  have H := memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
    (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) (B :=
    (‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2))^2) (by
      intro n
      have HD := identified_cheegerResolvent_davies hID hpar hfinite o h u ht (hV.min_const (n:ℝ))
        (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) hsmall
      have HU := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
      exact pow_le_pow_left₀ (norm_nonneg _) (HD.trans
        (div_le_div_of_nonneg_right HU (sub_pos.mpr hsmall).le)) 2)
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) (sub_pos.mpr hsmall).le)).mp
  rw [norm_toLp_sq_eq_integral]
  exact H.2

lemma identified_cheegerHeat_davies
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ‖expMulLp hV.continuous.aestronglyMeasurable hB (cheegerHeat h t u)‖^2 ≤
      ‖expMulLp hV.continuous.aestronglyMeasurable hB u‖^2*Real.exp (2*(L:ℝ)^2*t) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  let T := expMulLp hV.continuous.aestronglyMeasurable hB
  have hd : Dense (Q.resolventLinear.toLinearMap.range : Set (Lp ℝ 2 m)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (Q.resolvent_range_dense (cheeger_domain_dense h))
  apply hd.induction (P := fun v => ‖T (cheegerHeat h t v)‖^2 ≤ ‖T v‖^2*Real.exp (2*(L:ℝ)^2*t)) ?_ ?_ u
  · rintro v ⟨w,rfl⟩
    exact identified_cheegerHeat_davies_generator hID hpar hfinite o h (Q.isFormGenerator_resolvent w) hV hB ht
  · exact isClosed_le ((T.continuous.comp (cheegerHeat h t).continuous).norm.pow 2)
      ((T.continuous.norm.pow 2).mul_const _)

lemma identified_cheegerHeat_weighted
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun x => cheegerHeat h t u x*Real.exp (V x)) 2 m ∧
      (∫ x, (cheegerHeat h t u x*Real.exp (V x))^2 ∂m) ≤
        ‖hU.toLp (fun x => u x*Real.exp (V x))‖^2*Real.exp (2*(L:ℝ)^2*t) := by
  apply memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
  intro n
  have H := identified_cheegerHeat_davies hID hpar hfinite o h u (hV.min_const (n:ℝ))
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) ht
  exact H.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n) 2)
    (Real.exp_pos _).le)

lemma identified_cheegerHeat_weighted_norm
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    ‖(identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1.toLp
        (fun x => cheegerHeat h t u x*Real.exp (V x))‖ ≤
      ‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_toLp_sq_eq_integral,mul_pow,sq_exp_eq]
  have H := (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).2
  simpa only [mul_assoc] using H

lemma identified_cheegerHeat_laplacian_integral_zero
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, cheegerHeat h t A x ∂m) = 0 := by
  have hUt := (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1
  have hAt := (identified_cheegerHeat_weighted hID hpar hfinite o h A hV hA ht).1
  have hpar := hpar
  have hLap := identified_isLaplacian_of_formGenerator hfinite hID h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  exact hLap.integral_eq_zero hfinite hpar o (integrable_of_memLp_mul_exp hAt hdecay)
    (integrable_of_memLp_mul_exp (hLap.memLp_gradient_mul_exp hfinite hpar hV hUt hAt) hdecay)

lemma identified_cheegerHeat_mass_weighted_generator
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, cheegerHeat h t u x ∂m) = ∫ x, u x ∂m := by
  let C := ‖hA.toLp (fun x => A x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t)*
      ‖hdecay.toLp (fun x => Real.exp (-V x))‖
  let fn : ℕ → ℝ → ℝ := fun n s => ∫ x, cheegerHeat h s A x*radialCutoff o n x ∂m
  have hfn (n : ℕ) : ContinuousOn (fn n) (Ici 0) := by
    have he : fn n = fun s => (innerSL ℝ (radialCutoffLp hfinite o n)) (cheegerHeat h s A) := by
      funext s; exact integral_radialCutoff_eq_inner hfinite o n _
    rw [he]
    exact (innerSL ℝ (radialCutoffLp hfinite o n)).continuous.comp_continuousOn
      (cheegerHeat_continuousOn hfinite h A)
  have hb (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 t) : ‖fn n s‖ ≤ C := by
    have hsW := (identified_cheegerHeat_weighted hID hpar hfinite o h A hV hA hs.1).1
    have HH := integral_cutoff_le_weighted hsW hdecay
      (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa only [abs_of_nonneg (radialCutoff_nonneg o n x)] using radialCutoff_le_one o n x)
    apply HH.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (identified_cheegerHeat_weighted_norm hID hpar hfinite o h A hV hA hs.1).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _))
  have hlim (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun n => fn n s) atTop (𝓝 0) := by
    have H := integral_radialCutoff_tendsto o
      (integrable_of_memLp_mul_exp (identified_cheegerHeat_weighted hID hpar hfinite o h A hV hA hs).1 hdecay)
    rw [identified_cheegerHeat_laplacian_integral_zero hID hpar hfinite o h hu hV hU hA hdecay hs] at H
    exact H
  have htime : Tendsto (fun n => ∫ s in 0..t, fn n s) atTop (𝓝 0) := by
    have H := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := t) (f := fun _ => (0:ℝ)) (fun _ => C)
      (Eventually.of_forall (fun n =>
        ((hfn n).mono (show uIoc (0:ℝ) t ⊆ Ici 0 by rw [uIoc_of_le ht]; exact fun _ hx => hx.1.le)).aestronglyMeasurable measurableSet_uIoc))
      (Eventually.of_forall (fun n => ae_of_all _ fun s hs =>
        hb n s (by rw [uIoc_of_le ht] at hs; exact ⟨hs.1.le,hs.2⟩)))
      (intervalIntegrable_const)
      (ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le ht] at hs; exact hs.1.le))
    simpa only [intervalIntegral.integral_zero] using H
  have hFTC (n : ℕ) : (∫ s in 0..t, fn n s) =
      (∫ x, cheegerHeat h t u x*radialCutoff o n x ∂m)-(∫ x, u x*radialCutoff o n x ∂m) := by
    let T := innerSL ℝ (radialCutoffLp hfinite o n)
    have hAint : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t := ((cheegerHeat_continuousOn hfinite h A).mono
      (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
    have H := congrArg T (cheegerHeat_integral_generator hfinite h hu ht)
    rw [← T.intervalIntegral_comp_comm hAint,map_sub] at H
    simpa only [T,innerSL_apply_apply,← integral_radialCutoff_eq_inner hfinite o n] using H
  have hsp := (integral_radialCutoff_tendsto o
    (integrable_of_memLp_mul_exp (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1 hdecay)).sub
      (integral_radialCutoff_tendsto o (integrable_of_memLp_mul_exp hU hdecay))
  rw [show (fun n => ∫ s in 0..t, fn n s) = (fun n =>
    (∫ x, cheegerHeat h t u x*radialCutoff o n x ∂m)-(∫ x, u x*radialCutoff o n x ∂m)) from funext hFTC] at htime
  exact sub_eq_zero.mp (tendsto_nhds_unique hsp htime)

lemma identified_cheegerHeat_mass_of_weighted_resolvents
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    {ts : ℕ → ℝ} (hpos : ∀ n, 0 < ts n)
    (hsmall : ∀ n, ts n*(L:ℝ)^2 ≤ 1/2) (hlim : Tendsto ts atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  let us : ℕ → Lp ℝ 2 m := fun n => (Q.scale (hpos n)).resolventLinear u
  let As : ℕ → Lp ℝ 2 m := fun n => (ts n)⁻¹ • (us n-u)
  have hsmall' (n : ℕ) : ts n*(L:ℝ)^2 < 1 := (hsmall n).trans_lt (by norm_num)
  have hus (n : ℕ) : Q.IsFormGenerator (us n) (As n) :=
    (Q.scaled_resolvent_iff (hpos n) u (us n)).mp rfl
  have hW (n : ℕ) : MemLp (fun x => us n x*Real.exp (V x)) 2 m :=
    identified_cheegerResolvent_weighted hID hpar hfinite o h u (hpos n) hV hU (hsmall' n)
  have hWnorm (n : ℕ) : ‖(hW n).toLp (fun x => us n x*Real.exp (V x))‖ ≤
      2*‖hU.toLp (fun x => u x*Real.exp (V x))‖ := by
    apply (identified_cheegerResolvent_weighted_norm hID hpar hfinite o h u (hpos n) hV hU (hsmall' n)).trans
    apply (div_le_iff₀ (sub_pos.mpr (hsmall' n))).mpr
    have H := mul_le_mul_of_nonneg_left (hsmall n) (norm_nonneg (hU.toLp _))
    nlinarith
  have hAw (n : ℕ) : MemLp (fun x => As n x*Real.exp (V x)) 2 m := by
    have H := ((hW n).sub hU).const_smul ((ts n)⁻¹)
    apply MemLp.ae_eq _ H
    filter_upwards [Lp.coeFn_smul ((ts n)⁻¹) (us n-u),Lp.coeFn_sub (us n) u] with x hs hd
    dsimp only [As]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hd]
    simp only [Pi.sub_apply]
    ring
  have hum : Tendsto us atTop (𝓝 u) := Q.scaled_resolvent_tendsto (cheeger_domain_dense h) hpos hlim u
  have H1 := integral_tendsto_of_weighted_bound hdecay hfinite o hum hU hW hWnorm
  have hWt (n : ℕ) := (identified_cheegerHeat_weighted hID hpar hfinite o h (us n) hV (hW n) ht).1
  have hWtnorm (n : ℕ) : ‖(hWt n).toLp (fun x => cheegerHeat h t (us n) x*Real.exp (V x))‖ ≤
      (2*‖hU.toLp (fun x => u x*Real.exp (V x))‖)*Real.exp ((L:ℝ)^2*t) := by
    exact (identified_cheegerHeat_weighted_norm hID hpar hfinite o h (us n) hV (hW n) ht).trans
      (mul_le_mul_of_nonneg_right (hWnorm n) (Real.exp_pos _).le)
  have H2 := integral_tendsto_of_weighted_bound hdecay hfinite o
    ((cheegerHeat h t).continuous.continuousAt.tendsto.comp hum)
    (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1 hWt hWtnorm
  have he (n : ℕ) : (∫ x,cheegerHeat h t (us n) x ∂m) = ∫ x,us n x ∂m :=
    identified_cheegerHeat_mass_weighted_generator hID hpar hfinite o h (hus n) hV (hW n) (hAw n) hdecay ht
  simp_rw [Function.comp_def,he] at H2
  exact tendsto_nhds_unique H2 H1

lemma identified_cheegerHeat_mass_localized
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  let ts : ℕ → ℝ := fun n => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))
  have hpos (n : ℕ) : 0 < ts n := by dsimp only [ts]; positivity
  have hlim : Tendsto ts atTop (𝓝 0) := by
    have H : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))) atTop (𝓝 ((0:ℝ)/(2*((L:ℝ)^2+1)))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2*((L:ℝ)^2+1))
    simpa only [zero_div] using H
  have hsmall (n : ℕ) : ts n*(L:ℝ)^2 ≤ 1/2 := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hden : 0 < 2*((L:ℝ)^2+1) := by positivity
    have h1 : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp only [ts]
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    have H := mul_le_mul_of_nonneg_right h1 (sq_nonneg (L:ℝ))
    nlinarith
  exact identified_cheegerHeat_mass_of_weighted_resolvents hID hpar hfinite o h u hV hU hdecay hpos hsmall hlim ht

end WeakHessian

end
end InlinedFile216

end OAI
