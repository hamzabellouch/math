import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace OAI

section

/-! # Quantitative chart estimates for the finite-gain pullback

A normalized derivative within one half of the identity gives an injective
chart. A positive Jacobian lower bound then controls pullback integrals,
including arbitrary bounded measurable masks in the parameter density.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.GainPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chart_injective {s : Set E} (hs : Convex ℝ s)
    {f : E → E} {f' : E → E →L[ℝ] E} (A : E ≃L[ℝ] E)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hclose : ∀ x ∈ s,
      ‖A.symm.toContinuousLinearMap.comp (f' x) - ContinuousLinearMap.id ℝ E‖ ≤ 1/2) :
    InjOn f s := by
  intro x hx y hy hxy
  have hder (z) (hz : z ∈ s) :
      HasFDerivWithinAt (fun w => A.symm (f w))
        (A.symm.toContinuousLinearMap.comp (f' z)) s z :=
    A.symm.toContinuousLinearMap.hasFDerivAt.comp_hasFDerivWithinAt z (hf z hz)
  have h := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' hder hclose hx hy
  simp only [hxy,sub_self,ContinuousLinearMap.id_apply,zero_sub,norm_neg] at h
  have hn : ‖y-x‖ = 0 := by nlinarith [norm_nonneg (y-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

theorem jacobian_pullback_bound {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hi : InjOn f s)
    {c : ℝ} (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(f' x).det|)
    (g : E → ℝ≥0∞) :
    ∫⁻ x in s, g (f x) ∂μ ≤ (ENNReal.ofReal c)⁻¹ * ∫⁻ y in f '' s, g y ∂μ := by
  have hbound : ENNReal.ofReal c * (∫⁻ x in s, g (f x) ∂μ) ≤
      ∫⁻ y in f '' s, g y ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hf hi g]
    apply setLIntegral_mono' hs
    intro x hx
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hdet x hx)) le_rfl
  calc
    _ = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * ∫⁻ x in s, g (f x) ∂μ) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel
        (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hbound

theorem masked_jacobian_pullback_bound {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hi : InjOn f s)
    {c : ℝ} (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(f' x).det|)
    (g ρ : E → ℝ≥0∞) {B : ℝ≥0∞} (hB : B ≠ ∞) (hρ : ∀ x ∈ s, ρ x ≤ B) :
    ∫⁻ x in s, ρ x * g (f x) ∂μ ≤
      (B * (ENNReal.ofReal c)⁻¹) * ∫⁻ y in f '' s, g y ∂μ := by
  calc
    _ ≤ ∫⁻ x in s, B * g (f x) ∂μ := by
      apply setLIntegral_mono' hs
      intro x hx
      exact mul_le_mul' (hρ x hx) le_rfl
    _ = B * ∫⁻ x in s, g (f x) ∂μ := by rw [lintegral_const_mul' _ _ hB]
    _ ≤ B * ((ENNReal.ofReal c)⁻¹ * ∫⁻ y in f '' s, g y ∂μ) :=
      mul_le_mul' le_rfl (jacobian_pullback_bound hs hf hi hc hdet g)
    _ = _ := by rw [mul_assoc]

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # A regular chart persists under locally uniform convergence of derivatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem regular_derivative_neighborhood (A : E ≃L[ℝ] E)
    (hA : 0 < |A.toContinuousLinearMap.det|) :
    ∃ δ > 0, ∀ B : E →L[ℝ] E, ‖B-A.toContinuousLinearMap‖ < δ →
      ‖A.symm.toContinuousLinearMap.comp B - ContinuousLinearMap.id ℝ E‖ ≤ 1/2 ∧
      |A.toContinuousLinearMap.det|/2 ≤ |B.det| := by
  have hcomp : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by ext x; simp
  have hN : Continuous (fun B : E →L[ℝ] E =>
      ‖A.symm.toContinuousLinearMap.comp B - ContinuousLinearMap.id ℝ E‖) := by fun_prop
  have hD : Continuous (fun B : E →L[ℝ] E => |B.det|) :=
    ContinuousLinearMap.continuous_det.abs
  have hn := hN.continuousAt.eventually (Iio_mem_nhds (show
      ‖A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap -
        ContinuousLinearMap.id ℝ E‖ < 1/2 by rw [hcomp,sub_self,norm_zero]; norm_num))
  have hd := hD.continuousAt.eventually
    (Ioi_mem_nhds (show |A.toContinuousLinearMap.det|/2 < |A.toContinuousLinearMap.det| by linarith))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hn.and hd)
  refine ⟨δ,hδ,fun B hB => ?_⟩
  have h := hball (show B ∈ ball A.toContinuousLinearMap δ by
    simpa only [mem_ball,dist_eq_norm] using hB)
  exact ⟨h.1.le,h.2.le⟩

/-- On a small ball at a regular point, all sufficiently late charts are
injective with one common positive Jacobian lower bound. -/
theorem eventually_regular_ball {O : Set E} (hO : IsOpen O) {x₀ : E} (hx₀ : x₀ ∈ O)
    {f' : E → E →L[ℝ] E} (hcont : ContinuousAt f' x₀)
    (A : E ≃L[ℝ] E) (hAt : f' x₀ = A.toContinuousLinearMap)
    (hA : 0 < |A.toContinuousLinearMap.det|)
    {F : ℕ → E → E} {F' : ℕ → E → E →L[ℝ] E}
    (hF : ∀ n, ∀ x ∈ O, HasFDerivAt (F n) (F' n x) x)
    (hconv : ∀ r > 0, ball x₀ r ⊆ O →
      TendstoUniformlyOn F' f' atTop (ball x₀ r)) :
    ∃ r > 0, ball x₀ r ⊆ O ∧
      ∀ᶠ n in atTop, InjOn (F n) (ball x₀ r) ∧
        ∀ x ∈ ball x₀ r, |A.toContinuousLinearMap.det|/2 ≤ |(F' n x).det| := by
  obtain ⟨δ,hδ,hδspec⟩ := regular_derivative_neighborhood A hA
  have hnear : ∀ᶠ x in 𝓝 x₀, ‖f' x-A.toContinuousLinearMap‖ < δ/2 := by
    have h := hcont.eventually (Metric.ball_mem_nhds (f' x₀) (half_pos hδ))
    simpa only [mem_ball,dist_eq_norm,hAt] using h
  obtain ⟨r,hr,hrspec⟩ := Metric.mem_nhds_iff.mp (hnear.and (hO.mem_nhds hx₀))
  have hsub : ball x₀ r ⊆ O := fun x hx => (hrspec hx).2
  refine ⟨r,hr,hsub,?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hconv r hr hsub)) (δ/2) (half_pos hδ)] with n hn
  have hbound (x) (hx : x ∈ ball x₀ r) : ‖F' n x-A.toContinuousLinearMap‖ < δ := by
    have h₁ : ‖F' n x-f' x‖ < δ/2 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hn x hx
    have h₂ := (hrspec hx).1
    calc
      _ ≤ ‖F' n x-f' x‖+‖f' x-A.toContinuousLinearMap‖ := by
        simpa only [dist_eq_norm] using
          dist_triangle (F' n x) (f' x) A.toContinuousLinearMap
      _ < δ := by linarith
  refine ⟨chart_injective (convex_ball x₀ r) A
    (fun x hx => (hF n x (hsub hx)).hasFDerivWithinAt)
    (fun x hx => (hδspec _ (hbound x hx)).1),?_⟩
  exact fun x hx => (hδspec _ (hbound x hx)).2

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Vanishing pullbacks on regular charts, with bounded parameter densities -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

theorem tendsto_masked_chart_zero {s : Set E} (hs : MeasurableSet s)
    {F : ℕ → E → E} {F' : ℕ → E → E →L[ℝ] E}
    {g ρ : ℕ → E → ℝ≥0∞} {c : ℝ} (hc : 0 < c)
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hchart : ∀ᶠ n in atTop,
      (∀ x ∈ s, HasFDerivWithinAt (F n) (F' n x) s x) ∧
      InjOn (F n) s ∧ (∀ x ∈ s, c ≤ |(F' n x).det|) ∧
      (∀ x ∈ s, ρ n x ≤ B))
    (hg : Tendsto (fun n => ∫⁻ y, g n y ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in s, ρ n x * g n (F n x) ∂μ) atTop (𝓝 0) := by
  have hfinite : B*(ENNReal.ofReal c)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top hB (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hc)))
  have hscale := ENNReal.Tendsto.const_mul (a := B*(ENNReal.ofReal c)⁻¹) hg (Or.inr hfinite)
  simp only [mul_zero] at hscale
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hchart] with n hn
  apply (masked_jacobian_pullback_bound hs hn.1 hn.2.1 hc hn.2.2.1 (g n) (ρ n) hB hn.2.2.2).trans
  exact mul_le_mul' le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl)

theorem masked_exception_bound {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {s : Set X} (hs : MeasurableSet s) {g ρ : X → ℝ≥0∞} {F : X → X}
    {B M : ℝ≥0∞} (hρ : ∀ x ∈ s, ρ x ≤ B) (hg : ∀ x ∈ s, g (F x) ≤ M) :
    ∫⁻ x in s, ρ x * g (F x) ∂ν ≤ (B*M)*ν s := by
  calc
    _ ≤ ∫⁻ _x in s, B*M ∂ν := by
      apply setLIntegral_mono' hs
      intro x hx
      exact mul_le_mul' (hρ x hx) (hg x hx)
    _ = _ := by simp

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Gluing local pullback convergence outside a null critical set -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

theorem lintegral_finite_union_le {X I : Type*} [MeasurableSpace X]
    {μ : Measure X} (s : Finset I) (U : I → Set X) (f : X → ℝ≥0∞) :
    ∫⁻ x in ⋃ i ∈ s, U i, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in U i, f x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [show (⋃ j ∈ insert i s, U j) = U i ∪ ⋃ j ∈ s, U j by simp,
      Finset.sum_insert hi]
    exact (lintegral_union_le f _ _).trans (add_le_add le_rfl ih)

/-- Local integral convergence on a neighborhood of each noncritical point
suffices on a compact set, provided the integrands have a common bound. -/
theorem compact_integral_zero_of_local {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    {μ : Measure X} [OuterRegular μ] {K Z : Set X} (hK : IsCompact K)
    (hZ : μ Z = 0) {f : ℕ → X → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbound : ∀ n x, x ∈ K → f n x ≤ M)
    (hlocal : ∀ x ∈ K \ Z, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      Tendsto (fun n => ∫⁻ y in U, f n y ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, f n x ∂μ) atTop (𝓝 0) := by
  classical
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hhalf : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨δ,hδ,hδsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hM hhalf.ne'
  obtain ⟨Bad,hZBad,hBad,hBadsmall⟩ := Z.exists_isOpen_lt_of_lt (μ := μ) δ (by
    rw [hZ]; exact ENNReal.coe_pos.mpr hδ)
  let R := {x // x ∈ K \ Z}
  have hchoice (x : R) := hlocal x x.2
  choose U hUopen hUmem hUlim using hchoice
  have hcover : K \ Bad ⊆ ⋃ x : R, U x := by
    intro x hx
    have hxR : x ∈ K \ Z := ⟨hx.1,fun hz => hx.2 (hZBad hz)⟩
    exact mem_iUnion.mpr ⟨⟨x,hxR⟩,hUmem ⟨x,hxR⟩⟩
  obtain ⟨I,hI⟩ := (hK.diff hBad).elim_finite_subcover U hUopen hcover
  have hsum : Tendsto (fun n => ∑ i ∈ I, ∫⁻ x in U i, f n x ∂μ) atTop (𝓝 0) := by
    have h := tendsto_finsetSum I (fun i _ => hUlim i)
    simpa using h
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hsum (ε/2) hhalf] with n hn
  have hKB : (∫⁻ x in K ∩ Bad, f n x ∂μ) ≤ M*μ Bad := by
    apply (show (∫⁻ x in K ∩ Bad, f n x ∂μ) ≤ M*μ (K ∩ Bad) from ?_).trans
      (mul_le_mul' le_rfl (measure_mono inter_subset_right))
    calc
      _ ≤ ∫⁻ _x in K ∩ Bad, M ∂μ := by
        apply setLIntegral_mono' (hK.measurableSet.inter hBad.measurableSet)
        intro x hx
        exact hbound n x hx.1
      _ = _ := by simp
  have hset : K ⊆ (K ∩ Bad) ∪ ⋃ i ∈ I, U i := by
    intro x hx
    by_cases hb : x ∈ Bad
    · exact Or.inl ⟨hx,hb⟩
    · exact Or.inr (hI ⟨hx,hb⟩)
  calc
    _ ≤ ∫⁻ x in (K ∩ Bad) ∪ ⋃ i ∈ I, U i, f n x ∂μ := lintegral_mono_set hset
    _ ≤ (∫⁻ x in K ∩ Bad, f n x ∂μ) + ∫⁻ x in ⋃ i ∈ I, U i, f n x ∂μ :=
      lintegral_union_le _ _ _
    _ ≤ M*μ Bad + ∑ i ∈ I, ∫⁻ x in U i, f n x ∂μ :=
      add_le_add hKB (lintegral_finite_union_le I U (f n))
    _ ≤ ε/2+ε/2 := add_le_add
      ((mul_le_mul' le_rfl hBadsmall.le).trans (by simpa [mul_comm] using hδsmall.le)) hn
    _ = ε := ENNReal.add_halves ε

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Pullback estimates after adjoining the unused parameter coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]

theorem product_chart_bound {s : Set (P × Q)} (hs : MeasurableSet s)
    {F : P × Q → P × Q} {F' : P × Q → (P × Q) →L[ℝ] P × Q}
    (hf : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x) (hi : InjOn F s)
    {c : ℝ} (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(F' x).det|)
    {W : Set Q} (hWfin : volume W ≠ ∞)
    (himage : ∀ x ∈ s, (F x).2 ∈ W)
    (g : P → ℝ≥0∞) (hg : Measurable g) (ρ : P × Q → ℝ≥0∞)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hρ : ∀ x ∈ s, ρ x ≤ B) :
    ∫⁻ x in s, ρ x * g (F x).1 ∂((volume : Measure P).prod volume) ≤
      ((B*(ENNReal.ofReal c)⁻¹)*volume W) * ∫⁻ y, g y := by
  have hmain := masked_jacobian_pullback_bound
    (μ := (volume : Measure P).prod volume) hs hf hi hc hdet
    (fun y => g y.1) ρ hB hρ
  have hsub : F '' s ⊆ (univ : Set P) ×ˢ W := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨mem_univ _,himage x hx⟩
  have hproduct : (∫⁻ y in (univ : Set P) ×ˢ W, g y.1
      ∂((volume : Measure P).prod volume)) = volume W * ∫⁻ y, g y := by
    rw [setLIntegral_prod (fun y : P × Q => g y.1) (by fun_prop)]
    simp only [lintegral_const,Measure.restrict_apply_univ,Measure.restrict_univ]
    rw [lintegral_mul_const' _ _ hWfin,mul_comm]
  calc
    _ ≤ (B*(ENNReal.ofReal c)⁻¹) * (∫⁻ y in F '' s, g y.1
        ∂((volume : Measure P).prod volume)) := hmain
    _ ≤ (B*(ENNReal.ofReal c)⁻¹) * (∫⁻ y in (univ : Set P) ×ˢ W, g y.1
        ∂((volume : Measure P).prod volume)) := mul_le_mul' le_rfl (lintegral_mono_set hsub)
    _ = _ := by rw [hproduct]; ac_rfl

theorem tendsto_product_chart_zero {s : Set (P × Q)} (hs : MeasurableSet s)
    {F : ℕ → P × Q → P × Q} {F' : ℕ → P × Q → (P × Q) →L[ℝ] P × Q}
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → P × Q → ℝ≥0∞}
    {c : ℝ} (hc : 0 < c) {B : ℝ≥0∞} (hB : B ≠ ∞)
    {W : Set Q} (hWfin : volume W ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hchart : ∀ᶠ n in atTop,
      (∀ x ∈ s, HasFDerivWithinAt (F n) (F' n x) s x) ∧
      InjOn (F n) s ∧ (∀ x ∈ s, c ≤ |(F' n x).det|) ∧
      (∀ x ∈ s, (F n x).2 ∈ W) ∧ (∀ x ∈ s, ρ n x ≤ B))
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in s, ρ n x*g n (F n x).1
      ∂((volume : Measure P).prod volume)) atTop (𝓝 0) := by
  have hfinite : (B*(ENNReal.ofReal c)⁻¹)*volume W ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hB
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hc)))) hWfin
  have hscale := ENNReal.Tendsto.const_mul (a := (B*(ENNReal.ofReal c)⁻¹)*volume W)
    hL (Or.inr hfinite)
  simp only [mul_zero] at hscale
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hchart] with n hn
  exact product_chart_bound hs hn.1 hn.2.1 hc hn.2.2.1 hWfin hn.2.2.2.1
    (g n) (hg n) (ρ n) hB hn.2.2.2.2

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Local pullback convergence after adjoining a complementary projection -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

section Derivatives
variable {E P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem augmented_derivative_uniform {s : Set E}
    {F : ℕ → E → E →L[ℝ] P} {f : E → E →L[ℝ] P}
    (h : TendstoUniformlyOn F f atTop s) (π : E →L[ℝ] Q) :
    TendstoUniformlyOn (fun n x => (F n x).prod π) (fun x => (f x).prod π) atTop s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h ε hε] with n hn
  intro x hx
  have he : (f x).prod π-(F n x).prod π = (f x-F n x).prod 0 := by
    ext y <;> simp
  simpa only [dist_eq_norm,he,ContinuousLinearMap.opNorm_prod,Prod.norm_def,norm_zero,
    max_eq_left (norm_nonneg _)] using hn x hx

end Derivatives

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]
local notation "E" => P × Q

theorem local_augmented_pullback_zero {O : Set E} (hO : IsOpen O) {x₀ : E} (hx₀ : x₀ ∈ O)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ContinuousAt φ' x₀) (π : E →L[ℝ] Q) (A : E ≃L[ℝ] E)
    (hA : (φ' x₀).prod π = A.toContinuousLinearMap)
    (hconv : ∀ r > 0, ball x₀ r ⊆ O → TendstoUniformlyOn Φ' φ' atTop (ball x₀ r))
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hg : ∀ n, Measurable (g n)) (hρ : ∀ n x, x ∈ O → ρ n x ≤ B)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    ∃ r > 0, ball x₀ r ⊆ O ∧ Tendsto
      (fun n => ∫⁻ x in ball x₀ r, ρ n x*g n (Φ n x)
        ∂((volume : Measure P).prod volume)) atTop (𝓝 0) := by
  let G (n : ℕ) (x : E) : E := (Φ n x,π x)
  let G' (n : ℕ) (x : E) : E →L[ℝ] E := (Φ' n x).prod π
  have hG (n) (x) (hx : x ∈ O) : HasFDerivAt (G n) (G' n x) x :=
    (hder n x hx).prodMk π.hasFDerivAt
  have hc : ContinuousAt (fun x => (φ' x).prod π) x₀ :=
    (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) ℝ).continuous.continuousAt.comp
      (hcont.prodMk continuousAt_const)
  have ha : 0 < |A.toContinuousLinearMap.det| := abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero
  obtain ⟨r,hr,hrO,hevent⟩ := eventually_regular_ball hO hx₀ hc A hA ha hG
    (fun r hr hrO => augmented_derivative_uniform (hconv r hr hrO) π)
  let W : Set Q := closedBall 0 (‖π‖*(‖x₀‖+r))
  have hWfin : volume W ≠ ∞ := (isCompact_closedBall (0 : Q) _).measure_lt_top.ne
  have hW (x : E) (hx : x ∈ ball x₀ r) : π x ∈ W := by
    have hnorm : ‖x‖ ≤ ‖x₀‖+r := by
      have h := norm_le_norm_add_norm_sub x₀ x
      rw [norm_sub_rev x₀ x] at h
      have hxr : ‖x-x₀‖ < r := by simpa only [mem_ball,dist_eq_norm] using hx
      linarith
    change dist (π x) 0 ≤ ‖π‖*(‖x₀‖+r)
    rw [dist_zero_right]
    exact (π.le_opNorm x).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  refine ⟨r,hr,hrO,?_⟩
  apply tendsto_product_chart_zero (F := G) (F' := G') isOpen_ball.measurableSet
    (half_pos ha) hB hWfin hg ?_ hL
  filter_upwards [hevent] with n hn
  exact ⟨fun x hx => (hG n x (hrO hx)).hasFDerivWithinAt,
    hn.1,hn.2,hW,fun x hx => hρ n x (hrO hx)⟩

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Robust compact pullback convergence for submersions

Regularity is expressed by a complementary linear projection at each point.
The critical set is null. Parameter masks need only have a common bound.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]
local notation "E" => P × Q

theorem compact_submersion_pullback_zero {O K Z : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) (hZ : ((volume : Measure P).prod volume) Z = 0)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ∀ x ∈ O, ContinuousAt φ' x)
    (hreg : ∀ x ∈ K \ Z, ∃ π : E →L[ℝ] Q, ∃ A : E ≃L[ℝ] E,
      (φ' x).prod π = A.toContinuousLinearMap)
    (hconv : ∀ x ∈ O, ∀ r > 0, ball x r ⊆ O →
      TendstoUniformlyOn Φ' φ' atTop (ball x r))
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n x, x ∈ O → ρ n x ≤ B) (hgM : ∀ n y, g n y ≤ M)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, ρ n x*g n (Φ n x)
      ∂((volume : Measure P).prod volume)) atTop (𝓝 0) := by
  apply compact_integral_zero_of_local hK hZ (ENNReal.mul_ne_top hB hM)
    (fun n x hx => mul_le_mul' (hρ n x (hKO hx)) (hgM n _))
  intro x hx
  obtain ⟨π,A,hA⟩ := hreg x hx
  obtain ⟨r,hr,_,hlim⟩ := local_augmented_pullback_zero hO (hKO hx.1)
    hder (hcont x (hKO hx.1)) π A hA (hconv x (hKO hx.1)) hB hg hρ hL
  exact ⟨ball x r,isOpen_ball,mem_ball_self hr,hlim⟩

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Compact pullback convergence for almost everywhere regular square maps -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ] [OuterRegular μ]

/-- The square-map case of the robust pullback estimate. Neither the masks
nor the bounded integrands are required to converge pointwise. -/
theorem compact_regular_pullback_zero {O K Z : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) (hZ : μ Z = 0)
    {F : ℕ → E → E} {F' : ℕ → E → E →L[ℝ] E} {f' : E → E →L[ℝ] E}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (F n) (F' n x) x)
    (hcont : ∀ x ∈ O, ContinuousAt f' x)
    (hreg : ∀ x ∈ K \ Z, ∃ A : E ≃L[ℝ] E, f' x = A.toContinuousLinearMap)
    (hconv : ∀ x ∈ O, ∀ r > 0, ball x r ⊆ O →
      TendstoUniformlyOn F' f' atTop (ball x r))
    {g ρ : ℕ → E → ℝ≥0∞} {B M : ℝ≥0∞} (hB : B ≠ ∞) (hM : M ≠ ∞)
    (hρ : ∀ n x, x ∈ O → ρ n x ≤ B) (hg : ∀ n y, g n y ≤ M)
    (hL : Tendsto (fun n => ∫⁻ y, g n y ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, ρ n x*g n (F n x) ∂μ) atTop (𝓝 0) := by
  apply compact_integral_zero_of_local hK hZ (ENNReal.mul_ne_top hB hM)
    (fun n x hx => mul_le_mul' (hρ n x (hKO hx)) (hg n _))
  intro x hx
  obtain ⟨A,hAx⟩ := hreg x hx
  have hA : 0 < |A.toContinuousLinearMap.det| :=
    abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero
  obtain ⟨r,hr,hrO,hevent⟩ := eventually_regular_ball hO (hKO hx.1)
    (hcont x (hKO hx.1)) A hAx hA hder (hconv x (hKO hx.1))
  refine ⟨ball x r,isOpen_ball,mem_ball_self hr,?_⟩
  apply tendsto_masked_chart_zero (F' := F') isOpen_ball.measurableSet (half_pos hA) hB ?_ hL
  filter_upwards [hevent] with n hn
  exact ⟨fun y hy => (hder n y (hrO hy)).hasFDerivWithinAt,
    hn.1,hn.2,fun y hy => hρ n y (hrO hy)⟩

end BoltzmannNonuniqueness.GainPullback

end

end

end OAI
