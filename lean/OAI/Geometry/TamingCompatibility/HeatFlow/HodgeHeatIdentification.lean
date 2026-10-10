import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeHeatEvaluation
import OAI.Geometry.TamingCompatibility.Hodge.HodgeKernelCanonical

namespace OAI

section

section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include D hD in
lemma hodgeSpectral_ext (T U : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true)
    (he : ∀ (x : ℝ) (f : L2 A J α hs ht true),
      hodgeResolvent A J α hs ht 1 f = x • f → T f = U f) : T = U := by
  let L := T-U
  have hi : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x) ≤ L.ker := by
    apply iSup_le
    intro x f hf
    change T f-U f = 0
    exact sub_eq_zero.mpr (he x f (Module.End.mem_eigenspace_iff.mp hf))
  have hcl : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,
      hodgeResolvent_eigenspaces_total A J α hs ht D hD]
    simp
  have htop : ⊤ ≤ L.ker := by
    rw [← hcl]
    exact Submodule.topologicalClosure_minimal _ hi (ContinuousLinearMap.isClosed_ker L)
  ext f
  have hf : T f-U f = 0 := htop (Submodule.mem_top)
  exact sub_eq_zero.mp hf

lemma hodgeBoundedSpectralMultiplier_commutes (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true)
    (hT : ∀ f, hodgeResolvent A J α hs ht 1 (T f) = T (hodgeResolvent A J α hs ht 1 f)) :
    hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm * T =
      T * hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm := by
  apply hodgeSpectral_ext A J α hs ht D hD
  intro x f hx
  have hTx : hodgeResolvent A J α hs ht 1 (T f) = x • T f := by rw [hT, hx, map_smul]
  rw [mul_apply_eq_comp, mul_apply_eq_comp,
    hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD m K hK hm x (T f) hTx,
    hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD m K hK hm x f hx,
    map_smul]

lemma hodgeSpectralHeat_star (t : ℝ) (f : L2 A J α hs ht true) :
    hodgeSpectralHeat A J α hs ht D hD t (l2Star A J α hs ht f) =
      l2Star A J α hs ht (hodgeSpectralHeat A J α hs ht D hD t f) := by
  have he := hodgeBoundedSpectralMultiplier_commutes A J α hs ht D hD
    (hodgeHeatMultiplier t) 1 zero_le_one
    (fun x => (abs_of_pos (hodgeHeatMultiplier_pos t x)).trans_le (hodgeHeatMultiplier_le_one t x))
    (l2Star A J α hs ht) (hodgeResolvent_star A J α hs ht 1)
  exact congrArg (fun T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => T f) he

variable (D' : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD' : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D' p).source)

lemma hodgeBoundedSpectralMultiplier_canonical (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) :
    hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm =
      hodgeBoundedSpectralMultiplier A J α hs ht D' hD' m K hK hm := by
  apply hodgeSpectral_ext A J α hs ht D hD
  intro x f hx
  rw [hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD m K hK hm x f hx,
    hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D' hD' m K hK hm x f hx]

lemma hodgeSpectralHeat_canonical (t : ℝ) :
    hodgeSpectralHeat A J α hs ht D hD t = hodgeSpectralHeat A J α hs ht D' hD' t := by
  exact hodgeBoundedSpectralMultiplier_canonical A J α hs ht D hD D' hD'
    (hodgeHeatMultiplier t) 1 zero_le_one
    (fun x => (abs_of_pos (hodgeHeatMultiplier_pos t x)).trans_le (hodgeHeatMultiplier_le_one t x))

lemma hodgeHeatBoost_canonical (r : ℝ) :
    hodgeHeatBoost A J α hs ht D hD r = hodgeHeatBoost A J α hs ht D' hD' r := by
  exact hodgeBoundedSpectralMultiplier_canonical A J α hs ht D hD D' hD' _ _ _ _

variable [T2Space X]
variable {A J α hs ht D hD D' hD'}
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (C' : HodgeSmoothingCover A J α hs ht D' hD' r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma heatEvaluation_eq (u : MetricUnit g) : C.heatEvaluation g u = C'.heatEvaluation g u := by
  unfold heatEvaluation
  rw [C.evaluation_eq C' g u, hodgeHeatBoost_canonical A J α hs ht D hD D' hD']

lemma heatEvaluationVector_eq (u : MetricUnit g) :
    C.heatEvaluationVector g u = C'.heatEvaluationVector g u := by
  unfold heatEvaluationVector
  rw [C.heatEvaluation_eq C' g u]

lemma heatInnerKernel_eq (u v : MetricUnit g) : C.heatInnerKernel g u v = C'.heatInnerKernel g u v := by
  unfold heatInnerKernel
  rw [C.heatEvaluationVector_eq C' g u, C.heatEvaluationVector_eq C' g v]

lemma heatRegularize_eq (μ : Measure (MetricUnit g)) : C.heatRegularize g μ = C'.heatRegularize g μ := by
  unfold heatRegularize
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (C.heatEvaluationVector_eq C' g)
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

private def unitSymbol (x : ℝ) : ℝ := min 1 (max 0 x)
private lemma unitSymbol_bound (x : ℝ) : |unitSymbol x| ≤ 1 := by
  rw [abs_of_nonneg (le_min zero_le_one (le_max_left _ _))]
  exact min_le_left _ _

lemma hodgeResolvent_unit_spectral :
    hodgeResolvent A J α hs ht 1 =
      hodgeBoundedSpectralMultiplier A J α hs ht D hD unitSymbol 1 zero_le_one unitSymbol_bound := by
  apply hodgeSpectral_ext A J α hs ht D hD
  intro x f hx
  rw [hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD _ _ _ _ x f hx, hx]
  by_cases hf : f = 0
  · simp [hf]
  · obtain ⟨hx0,hx1⟩ := hodgeResolvent_eigenvalue_positive_le_one A J α hs ht f hf x hx
    rw [unitSymbol, max_eq_right hx0.le, min_eq_right hx1]

lemma hodgeResolvent_rate_repr (f : L2 A J α hs ht true) (x : ℝ) :
    hodgeSpectralRate x • (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
      (hodgeResolvent A J α hs ht 1 f) x =
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
      (f-hodgeResolvent A J α hs ht 1 f) x := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  have hc : E (hodgeResolvent A J α hs ht 1 f) x = unitSymbol x • E f x := by
    calc
      E (hodgeResolvent A J α hs ht 1 f) x = E
          (hodgeBoundedSpectralMultiplier A J α hs ht D hD unitSymbol 1 zero_le_one unitSymbol_bound f) x :=
        congrArg (fun v => E v x) (congrArg (fun T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => T f)
          (hodgeResolvent_unit_spectral A J α hs ht D hD))
      _ = _ := hodgeBoundedSpectralMultiplier_repr A J α hs ht D hD _ _ _ _ f x
  have hcval := congrArg Subtype.val hc
  have hsub : (E (f-hodgeResolvent A J α hs ht 1 f) x).val =
      (E f x).val-(E (hodgeResolvent A J α hs ht 1 f) x).val := by
    rw [map_sub]
    rfl
  apply Subtype.ext
  change hodgeSpectralRate x • (E (hodgeResolvent A J α hs ht 1 f) x).val =
    (E (f-hodgeResolvent A J α hs ht 1 f) x).val
  change (E (hodgeResolvent A J α hs ht 1 f) x).val = unitSymbol x • (E f x).val at hcval
  rw [hsub,hcval]
  by_cases hz : (E f x).val = 0
  · simp [hz]
  · have he : hodgeResolvent A J α hs ht 1 (E f x).val = x • (E f x).val :=
      Module.End.mem_eigenspace_iff.mp (E f x).property
    obtain ⟨hx0,hx1⟩ := hodgeResolvent_eigenvalue_positive_le_one A J α hs ht _ hz x he
    have hi : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr hx1
    have hscalar : hodgeSpectralRate x * unitSymbol x = 1-unitSymbol x := by
      rw [unitSymbol, max_eq_right hx0.le, min_eq_right hx1,
        hodgeSpectralRate, max_eq_right (sub_nonneg.mpr hi)]
      field_simp
    rw [smul_smul,hscalar,sub_smul,one_smul]

lemma hodgeSpectralHeat_inner_series (t : ℝ) (f g : L2 A J α hs ht true) :
    ⟪hodgeSpectralHeat A J α hs ht D hD t f,g⟫ =
      ∑' x : ℝ, hodgeHeatMultiplier t x *
        ⟪(hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv f x,
          (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv g x⟫ := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  rw [← E.inner_map_map, lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  rw [hodgeSpectralHeat_repr]
  exact real_inner_smul_left (E f x).val (E g x).val _

lemma hodgeHeatMultiplier_hasDerivAt (t x : ℝ) (ht' : 0 < t) :
    HasDerivAt (fun s => hodgeHeatMultiplier s x)
      (-hodgeSpectralRate x * hodgeHeatMultiplier t x) t := by
  have hlin : HasDerivAt (fun s : ℝ => -s*hodgeSpectralRate x) (-hodgeSpectralRate x) t := by
    simpa only [id_eq, Pi.neg_apply, neg_one_mul] using
      ((hasDerivAt_id t).neg).mul_const (hodgeSpectralRate x)
  have he := hlin.exp
  have hp : ∀ᶠ s : ℝ in 𝓝 t, 0 < s := Ioi_mem_nhds ht'
  have heq : (fun s => hodgeHeatMultiplier s x) =ᶠ[𝓝 t]
      (fun s => Real.exp (-s*hodgeSpectralRate x)) := hp.mono (fun s hs' => by
    simp only [hodgeHeatMultiplier, max_eq_left hs'.le])
  have hd : Real.exp (-t*hodgeSpectralRate x) * -hodgeSpectralRate x =
      -hodgeSpectralRate x * hodgeHeatMultiplier t x := by
    simp only [hodgeHeatMultiplier,max_eq_left ht'.le]
    ring
  rw [hd] at he
  exact he.congr_of_eventuallyEq heq

lemma heatScalarSeries_hasDerivAt (a b : ℝ → ℝ) (ha : Summable a) (hb : Summable b)
    (hr : ∀ x, hodgeSpectralRate x * a x = b x) (t : ℝ) (ht' : 0 < t) :
    HasDerivAt (fun s => ∑' x : ℝ, hodgeHeatMultiplier s x * a x)
      (-(∑' x : ℝ, hodgeHeatMultiplier t x * b x)) t := by
  have hd (x s : ℝ) (hsp : s ∈ Ioi (0:ℝ)) :
      HasDerivAt (fun z => hodgeHeatMultiplier z x * a x)
        (-hodgeHeatMultiplier s x * b x) s := by
    have hh := (hodgeHeatMultiplier_hasDerivAt s x hsp).mul_const (a x)
    have heq : (-hodgeSpectralRate x * hodgeHeatMultiplier s x) * a x =
        -hodgeHeatMultiplier s x * b x := by rw [← hr x]; ring
    rw [heq] at hh
    exact hh
  have hbound (x s : ℝ) (_hsp : s ∈ Ioi (0:ℝ)) :
      ‖-hodgeHeatMultiplier s x * b x‖ ≤ ‖b x‖ := by
    rw [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos (hodgeHeatMultiplier_pos s x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hodgeHeatMultiplier_le_one s x)
  have hsum0 : Summable (fun x => hodgeHeatMultiplier t x * a x) := by
    apply Summable.of_norm_bounded ha.norm
    intro x
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (hodgeHeatMultiplier_pos t x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hodgeHeatMultiplier_le_one t x)
  have hh := hasDerivAt_tsum_of_isPreconnected hb.norm isOpen_Ioi isPreconnected_Ioi
    hd hbound ht' hsum0 ht'
  have heq : (∑' x : ℝ, -hodgeHeatMultiplier t x * b x) =
      -(∑' x : ℝ, hodgeHeatMultiplier t x * b x) := by
    simp only [neg_mul,tsum_neg]
  rw [heq] at hh
  exact hh

lemma hodgeSpectralHeat_resolvent_hasDerivAt (f g : L2 A J α hs ht true)
    (t : ℝ) (ht' : 0 < t) :
    HasDerivAt (fun s => ⟪hodgeSpectralHeat A J α hs ht D hD s
      (hodgeResolvent A J α hs ht 1 f),g⟫)
      (-⟪hodgeSpectralHeat A J α hs ht D hD t
        (f-hodgeResolvent A J α hs ht 1 f),g⟫) t := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  let a := fun x : ℝ => ⟪E (hodgeResolvent A J α hs ht 1 f) x,E g x⟫
  let b := fun x : ℝ => ⟪E (f-hodgeResolvent A J α hs ht 1 f) x,E g x⟫
  have hr (x : ℝ) : hodgeSpectralRate x * a x = b x := by
    have hh := congrArg (fun v : Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x =>
      ⟪v.val,(E g x).val⟫) (hodgeResolvent_rate_repr A J α hs ht D hD f x)
    change ⟪hodgeSpectralRate x • (E (hodgeResolvent A J α hs ht 1 f) x).val,(E g x).val⟫ = b x at hh
    exact (real_inner_smul_left (E (hodgeResolvent A J α hs ht 1 f) x).val
      (E g x).val (hodgeSpectralRate x)).symm.trans hh
  have ha : Summable a := lp.summable_inner (E (hodgeResolvent A J α hs ht 1 f)) (E g)
  have hb : Summable b := lp.summable_inner (E (f-hodgeResolvent A J α hs ht 1 f)) (E g)
  have hh := heatScalarSeries_hasDerivAt a b ha hb hr t ht'
  convert hh using 1
  · funext s
    exact hodgeSpectralHeat_inner_series A J α hs ht D hD s _ g
  · exact congrArg Neg.neg (hodgeSpectralHeat_inner_series A J α hs ht D hD t _ g)

lemma hodgeSpectralHeat_smooth_hasDerivAt (a : PreL2 A J α hs ht true)
    (g : L2 A J α hs ht true) (t : ℝ) (ht' : 0 < t) :
    HasDerivAt (fun s => ⟪hodgeSpectralHeat A J α hs ht D hD s
      (smoothL2 A J α hs ht true a),g⟫)
      (-⟪hodgeSpectralHeat A J α hs ht D hD t
        (smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)),g⟫) t := by
  have hi := hodgeResolvent_differential_inverse A J α hs ht 1 zero_lt_one a
  simp only [one_pow,one_smul] at hi
  rw [map_add (smoothL2 A J α hs ht true)] at hi
  have hh := hodgeSpectralHeat_resolvent_hasDerivAt A J α hs ht D hD
    (smoothL2 A J α hs ht true a +
      smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)) g t ht'
  rw [hi, add_sub_cancel_left] at hh
  exact hh

lemma hodgeSpectralHeat_weak_hasDerivAt (f : L2 A J α hs ht true)
    (a : PreL2 A J α hs ht true) (t : ℝ) (ht' : 0 < t) :
    HasDerivAt (fun s => ⟪hodgeSpectralHeat A J α hs ht D hD s f,
      smoothL2 A J α hs ht true a⟫)
      (-⟪hodgeSpectralHeat A J α hs ht D hD t f,
        smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t := by
  have hh := hodgeSpectralHeat_smooth_hasDerivAt A J α hs ht D hD a f t ht'
  have he : (fun s => ⟪hodgeSpectralHeat A J α hs ht D hD s f,
      smoothL2 A J α hs ht true a⟫) =
      (fun s => ⟪hodgeSpectralHeat A J α hs ht D hD s
        (smoothL2 A J α hs ht true a),f⟫) := by
    funext s
    rw [hodgeSpectralHeat_symmetric]
    exact real_inner_comm _ _
  have hd : ⟪hodgeSpectralHeat A J α hs ht D hD t
      (smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)),f⟫ =
      ⟪hodgeSpectralHeat A J α hs ht D hD t f,
        smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ := by
    rw [hodgeSpectralHeat_symmetric]
    exact real_inner_comm _ _
  rw [← he,hd] at hh
  exact hh
end TamingCompatibility.GeometricHilbert
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.WeakHeat
open Set Filter MeasureTheory Metric
open scoped Topology RealInnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma integral_eq_of_dense_weak (S : Set H) (hS : Dense S) (f g : ℝ → H)
    {a b : ℝ} (hg : ContinuousOn g (uIcc a b))
    (hd : ∀ w ∈ S, ∀ t ∈ uIcc a b,
      HasDerivAt (fun s => ⟪f s,w⟫) ⟪g t,w⟫ t) :
    (∫ t in a..b, g t) = f b-f a := by
  have hi : IntervalIntegrable g volume a b := hg.intervalIntegrable
  have he (w : H) (hw : w ∈ S) : ⟪∫ t in a..b, g t,w⟫ = ⟪f b-f a,w⟫ := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (hd w hw)
      ((hg.inner continuousOn_const).intervalIntegrable)
    have hc := (innerSL ℝ w).intervalIntegral_comp_comm hi
    simp only [innerSL_apply_apply] at hc
    calc
      ⟪∫ t in a..b, g t,w⟫ = ⟪w,∫ t in a..b, g t⟫ := real_inner_comm _ _
      _ = ∫ t in a..b, ⟪w,g t⟫ := hc.symm
      _ = ∫ t in a..b, ⟪g t,w⟫ := intervalIntegral.integral_congr
        (fun _ _ => real_inner_comm _ _)
      _ = ⟪f b-f a,w⟫ := by rw [hh,inner_sub_left]
  have hclosed : _root_.IsClosed {w : H | ⟪∫ t in a..b, g t,w⟫ = ⟪f b-f a,w⟫} :=
    isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  have hsub := closure_minimal he hclosed
  rw [hS.closure_eq] at hsub
  exact ext_inner_right ℝ (fun w => hsub (mem_univ w))

lemma hasDerivAt_of_dense_weak (S : Set H) (hS : Dense S) (f g : ℝ → H)
    {U : Set ℝ} (hU : IsOpen U) (hconv : Convex ℝ U) (hg : ContinuousOn g U)
    (hd : ∀ w ∈ S, ∀ t ∈ U, HasDerivAt (fun s => ⟪f s,w⟫) ⟪g t,w⟫ t)
    {t : ℝ} (ht : t ∈ U) : HasDerivAt f (g t) t := by
  have he (s : ℝ) (hs : s ∈ U) : f s = f t + ∫ u in t..s, g u := by
    have hseg : uIcc t s ⊆ U := by simpa only [segment_eq_uIcc] using hconv.segment_subset ht hs
    have hh := integral_eq_of_dense_weak S hS f g (hg.mono hseg)
      (fun w hw u hu => hd w hw u (hseg hu))
    rw [hh]
    abel
  have hct := hg.continuousAt (hU.mem_nhds ht)
  have hm : StronglyMeasurableAtFilter g (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter hU hg t ht
  have hp := (intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable g volume t t from IntervalIntegrable.refl) hm hct).const_add (f t)
  apply hp.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds ht] with s hs
  exact he s hs

lemma zero_of_resolvent_weak (R : H →L[ℝ] H) (hRinj : Function.Injective R)
    (hRsym : ∀ u v, ⟪R u,v⟫ = ⟪u,R v⟫)
    (hRpos : ∀ u, ⟪R u,R u⟫ ≤ ⟪u,R u⟫)
    (S : Set H) (hS : Dense S) (U : ℝ → H) {T : ℝ} (hT : 0 ≤ T)
    (hU : ContinuousOn U (Icc 0 T)) (hzero : U 0 = 0)
    (hweak : ∀ a ∈ S, ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s => ⟪U s,R a⟫) (-⟪U t,a-R a⟫) t) :
    ∀ t ∈ Icc 0 T, U t = 0 := by
  let V : ℝ → H := fun t => R (U t)
  let G : ℝ → H := fun t => R (U t)-U t
  have hV : ContinuousOn V (Icc 0 T) := R.continuous.comp_continuousOn hU
  have hG : ContinuousOn G (Icc 0 T) := hV.sub hU
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt V (G t) t := by
    apply hasDerivAt_of_dense_weak S hS V G isOpen_Ioo (convex_Ioo 0 T)
      (hG.mono Ioo_subset_Icc_self) _ ht
    intro a ha s hs
    have hh := hweak a ha s hs
    have hf : (fun t => ⟪V t,a⟫) = (fun t => ⟪U t,R a⟫) := by
      funext t
      exact hRsym _ _
    rw [hf]
    convert! hh using 1
    simp only [G, inner_sub_left, inner_sub_right, hRsym, neg_sub]
  let E : ℝ → ℝ := fun t => ⟪V t,V t⟫
  have hEd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt E (2*⟪G t,V t⟫) t := by
    convert! (hd t ht).inner ℝ (hd t ht) using 1
    rw [real_inner_comm (V t) (G t)]
    ring
  have hEn (t : ℝ) (ht : t ∈ Ioo 0 T) : deriv E t ≤ 0 := by
    rw [(hEd t ht).deriv]
    have hp := hRpos (U t)
    dsimp [G,V]
    rw [inner_sub_left]
    linarith
  have hanti : AntitoneOn E (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) (hV.inner hV)
    · rw [interior_Icc]
      exact fun t ht => (hEd t ht).differentiableAt.differentiableWithinAt
    · simpa only [interior_Icc] using hEn
  intro t ht
  have hle := hanti ⟨le_rfl,hT⟩ ht ht.1
  have he0 : E 0 = 0 := by simp [E,V,hzero]
  rw [he0] at hle
  have hvt : V t = 0 := inner_self_eq_zero.mp (le_antisymm hle (real_inner_self_nonneg))
  apply hRinj
  simpa [V] using hvt

end TamingCompatibility.GeometricHilbert.WeakHeat
end

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in

lemma hodgeResolvent_energy_le (r : ℝ) (hr : 0 < r) (f : L2 A J α hs ht true) :
    ⟪hodgeResolvent A J α hs ht r f,hodgeResolvent A J α hs ht r f⟫ ≤
      ⟪f,hodgeResolvent A J α hs ht r f⟫ := by
  have he := hodgeWeakSolution_identity A J α hs ht r hr f
    (hodgeWeakSolution A J α hs ht r hr f)
  have hi : hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr f) =
      hodgeResolvent A J α hs ht r f := by rw [hodgeResolvent_eq]; rfl
  rw [hi] at he
  have hn := mul_nonneg (sq_nonneg r) (real_inner_self_nonneg (x :=
    hodgeWeakDerivative A J α hs ht (hodgeWeakSolution A J α hs ht r hr f)))
  linarith

include D hD in

lemma hodgeResolvent_smooth_core (a : PreL2 A J α hs ht true) :
    ∃ b : PreL2 A J α hs ht true,
      smoothL2 A J α hs ht true b = hodgeResolvent A J α hs ht 1
        (smoothL2 A J α hs ht true a) ∧
      smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht b) =
        smoothL2 A J α hs ht true a - smoothL2 A J α hs ht true b := by
  obtain ⟨b,hb⟩ := hodgeGraphResolvent_smooth A J α hs ht D hD 1 zero_lt_one 1 a
  have hi := congrArg (hodgeInclusion A J α hs ht) hb
  rw [hodgeInclusion_smooth,hodgeGraphResolvent_inclusion_power, pow_one,
    hodgeInclusion_smooth] at hi
  refine ⟨b,hi,?_⟩
  have hinv := hodgeResolvent_differential_inverse A J α hs ht 1 zero_lt_one b
  simp only [one_pow,one_smul] at hinv
  rw [map_add (smoothL2 A J α hs ht true)] at hinv
  have hsum := hodgeResolvent_injective A J α hs ht 1 zero_lt_one (hinv.trans hi)
  exact eq_sub_of_add_eq' hsum

include D hD in

lemma hodgeWeakHeat_zero (U : ℝ → L2 A J α hs ht true) {T : ℝ} (hT : 0 ≤ T)
    (hU : ContinuousOn U (Icc 0 T)) (hzero : U 0 = 0)
    (hweak : ∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
        (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t) :
    ∀ t ∈ Icc 0 T, U t = 0 := by
  apply WeakHeat.zero_of_resolvent_weak (hodgeResolvent A J α hs ht 1)
    (hodgeResolvent_injective A J α hs ht 1 zero_lt_one)
    (hodgeResolvent_symmetric A J α hs ht 1)
    (hodgeResolvent_energy_le A J α hs ht 1 zero_lt_one)
    (Set.range (smoothL2 A J α hs ht true)) (smoothL2_dense A J α hs ht true)
    U hT hU hzero
  rintro _ ⟨a,rfl⟩ t ht'
  obtain ⟨b,hb,hDb⟩ := hodgeResolvent_smooth_core A J α hs ht D hD a
  have hh := hweak b t ht'
  rw [hDb,hb] at hh
  exact hh

include D hD in

lemma hodgeWeakHeat_eq_spectral (f : L2 A J α hs ht true)
    (U : ℝ → L2 A J α hs ht true) {T : ℝ} (hT : 0 ≤ T)
    (hU : ContinuousOn U (Icc 0 T)) (hzero : U 0 = f)
    (hweak : ∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
        (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t) :
    ∀ t ∈ Icc 0 T, U t = hodgeSpectralHeat A J α hs ht D hD t f := by
  have hh := hodgeWeakHeat_zero A J α hs ht D hD
    (fun t => U t-hodgeSpectralHeat A J α hs ht D hD t f) hT
    (hU.sub (hodgeSpectralHeat_continuous A J α hs ht D hD f).continuousOn) ?_ ?_
  · intro t ht'
    exact sub_eq_zero.mp (hh t ht')
  · simp [hzero,hodgeSpectralHeat_zero]
  · intro a t ht'
    have hd := (hweak a t ht').sub
      (hodgeSpectralHeat_weak_hasDerivAt A J α hs ht D hD f a t ht'.1)
    convert! hd using 1
    · funext s
      exact inner_sub_left _ _ _
    · rw [inner_sub_left]
      ring

end TamingCompatibility.GeometricHilbert

end
end
end
end
end

end

end OAI
