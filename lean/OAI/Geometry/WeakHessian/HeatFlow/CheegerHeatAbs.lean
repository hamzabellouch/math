import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatMassNonneg
import OAI.Geometry.WeakHessian.Measure.TendstoIntegralNormSub

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma cheegerHeat_abs_le (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {t : ℝ} (ht : 0 ≤ t) : ∀ᵐ x ∂m, |cheegerHeat h t u x| ≤ cheegerHeat h t |u| x := by
  have hplus : ∀ᵐ x ∂m, u x ≤ |u| x := by
    filter_upwards [Lp.coeFn_abs u] with x hx
    rw [hx]; exact le_abs_self _
  have hminus : ∀ᵐ x ∂m, (-u) x ≤ |u| x := by
    filter_upwards [Lp.coeFn_abs u,Lp.coeFn_neg u] with x hx hy
    rw [hx,hy]; exact neg_le_abs _
  have H := cheegerHeat_order h ht (-u) |u| hminus
  rw [map_neg] at H
  filter_upwards [cheegerHeat_order h ht u |u| hplus,H,Lp.coeFn_neg (cheegerHeat h t u)] with x hp hn he
  rw [he] at hn
  exact abs_le.mpr ⟨by simpa only [Pi.neg_apply,neg_neg] using neg_le_neg hn,hp⟩

lemma cheegerHeat_integrable (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hi : Integrable u m)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (cheegerHeat h t u) m ∧
      (∫ x, ‖cheegerHeat h t u x‖ ∂m) ≤ ∫ x,‖u x‖ ∂m := by
  have hia : Integrable (fun x => (|u| : Lp ℝ 2 m) x) m := hi.abs.congr (Lp.coeFn_abs u).symm
  have hpa : ∀ᵐ x ∂m, 0 ≤ |u| x := (Lp.coeFn_abs u).mono fun x hx => hx ▸ abs_nonneg _
  have H := cheegerHeat_submass hfinite o h |u| hpa hia ht
  have hb : ∀ᵐ x ∂m, ‖cheegerHeat h t u x‖ ≤ cheegerHeat h t |u| x := cheegerHeat_abs_le h u ht
  have hj := H.1.mono' (Lp.memLp _).aestronglyMeasurable hb
  refine ⟨hj,(integral_mono_ae hj.norm H.1 hb).trans (H.2.trans_eq ?_)⟩
  exact integral_congr_ae ((Lp.coeFn_abs u).mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integrable_posPartLp (u : Lp ℝ 2 m) (hi : Integrable u m) :
    Integrable (Lp.posPart u : X → ℝ) m := by
  exact (hi.sup (integrable_zero X ℝ m)).congr (Lp.coeFn_posPart u).symm

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integrable_negPartLp (u : Lp ℝ 2 m) (hi : Integrable u m) :
    Integrable (Lp.negPart u : X → ℝ) m := by
  exact (hi.neg.sup (integrable_zero X ℝ m)).congr (show (fun x => max (-u x) 0) =ᵐ[m] Lp.negPart u from (Lp.coeFn_negPart_eq_max u).mono fun x hx => hx.symm)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma posPart_sub_negPartLp (u : Lp ℝ 2 m) : Lp.posPart u-Lp.negPart u = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (Lp.posPart u) (Lp.negPart u),Lp.coeFn_posPart u,Lp.coeFn_negPart_eq_max u] with x he hp hn
  simp only [he,Pi.sub_apply,hp,hn]
  rcases le_total (0:ℝ) (u x) with h|h
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
  · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h),zero_sub,neg_neg]

lemma cheegerHeat_pairing_bound (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hi : Integrable u m)
    {φ : X → ℝ} (_ : AEStronglyMeasurable φ m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, ‖φ x‖ ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ‖∫ x,cheegerHeat h t u x*φ x ∂m‖ ≤ B*(∫ x,‖u x‖ ∂m) := by
  have H := cheegerHeat_integrable hfinite o h u hi ht
  by_cases hm : m = 0
  · simp [hm]
  have hb0 : 0 ≤ B := by
    have : NeZero m := ⟨hm⟩
    obtain ⟨x,hx⟩ := hB.exists
    exact (norm_nonneg _).trans hx
  calc
    _ ≤ ∫ x, B*‖cheegerHeat h t u x‖ ∂m := by
      apply norm_integral_le_of_norm_le (H.1.norm.const_mul B)
      filter_upwards [hB] with x hx
      rw [norm_mul]
      simpa only [mul_comm B] using mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = B*(∫ x,‖cheegerHeat h t u x‖ ∂m) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left H.2 hb0
end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_L1_tendsto_nonneg {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {s : ι → ℝ} {t : ℝ}
    (hs : ∀ i, 0 ≤ s i) (ht : 0 ≤ t) (hst : Tendsto s l (𝓝 t)) :
    Tendsto (fun i => ∫ x,‖cheegerHeat h (s i) u x-cheegerHeat h t u x‖ ∂m) l (𝓝 0) := by
  have hL2 : Tendsto (fun i => cheegerHeat h (s i) u) l (𝓝 (cheegerHeat h t u)) :=
    ((cheegerHeat_continuousOn hfin h u) t ht).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hst,Eventually.of_forall hs⟩)
  have hm i := hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hu hi (hs i)
  have htM := hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hu hi ht
  apply tendsto_integral_norm_sub_of_nonneg_mass hL2
    (fun i => cheegerHeat_nonneg h (hs i) u hu) (cheegerHeat_nonneg h ht u hu)
    (fun i => (hm i).1) htM.1
  simp_rw [(hm _).2,htM.2]
  exact tendsto_const_nhds

lemma CurvatureDimension.cheegerHeat_L1_tendsto {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hi : Integrable u m)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {s : ι → ℝ} {t : ℝ}
    (hs : ∀ i, 0 ≤ s i) (ht : 0 ≤ t) (hst : Tendsto s l (𝓝 t)) :
    Tendsto (fun i => ∫ x,‖cheegerHeat h (s i) u x-cheegerHeat h t u x‖ ∂m) l (𝓝 0) := by
  have hp : ∀ᵐ x ∂m, 0 ≤ Lp.posPart u x := (Lp.coeFn_posPart u).mono fun x hx => hx ▸ le_max_right _ _
  have hn : ∀ᵐ x ∂m, 0 ≤ Lp.negPart u x := (Lp.coeFn_negPart_eq_max u).mono fun x hx => hx ▸ le_max_right _ _
  have hp1 := integrable_posPartLp u hi
  have hn1 := integrable_negPartLp u hi
  have hpt := hcd.cheegerHeat_L1_tendsto_nonneg hN hfull hfin o h _ hp hp1 hs ht hst
  have hnt := hcd.cheegerHeat_L1_tendsto_nonneg hN hfull hfin o h _ hn hn1 hs ht hst
  have he (r : ℝ) : (cheegerHeat h r u : X → ℝ) =ᵐ[m]
      fun x => cheegerHeat h r (Lp.posPart u) x-cheegerHeat h r (Lp.negPart u) x := by
    have H : cheegerHeat h r u = cheegerHeat h r (Lp.posPart u)-cheegerHeat h r (Lp.negPart u) := by
      rw [← map_sub, posPart_sub_negPartLp]
    rw [H]
    exact Lp.coeFn_sub _ _
  have hb i : (∫ x,‖cheegerHeat h (s i) u x-cheegerHeat h t u x‖ ∂m) ≤
      (∫ x,‖cheegerHeat h (s i) (Lp.posPart u) x-cheegerHeat h t (Lp.posPart u) x‖ ∂m)+
      (∫ x,‖cheegerHeat h (s i) (Lp.negPart u) x-cheegerHeat h t (Lp.negPart u) x‖ ∂m) := by
    have H1 := ((cheegerHeat_integrable hfin o h _ hp1 (hs i)).1.sub
      (cheegerHeat_integrable hfin o h _ hp1 ht).1).norm
    have H2 := ((cheegerHeat_integrable hfin o h _ hn1 (hs i)).1.sub
      (cheegerHeat_integrable hfin o h _ hn1 ht).1).norm
    simp only [Pi.sub_apply] at H1 H2
    rw [← integral_add H1 H2]
    apply integral_mono_ae (((cheegerHeat_integrable hfin o h _ hi (hs i)).1.sub
      (cheegerHeat_integrable hfin o h _ hi ht).1).norm) (H1.add H2)
    filter_upwards [he (s i),he t] with x hi' ht'
    dsimp only [Pi.add_apply,Pi.sub_apply]
    rw [hi',ht']
    convert norm_sub_le (cheegerHeat h (s i) (Lp.posPart u) x-cheegerHeat h t (Lp.posPart u) x)
      (cheegerHeat h (s i) (Lp.negPart u) x-cheegerHeat h t (Lp.negPart u) x) using 1
    congr 1
    ring
  apply squeeze_zero (fun i => integral_nonneg fun x => norm_nonneg _) hb
  simpa only [add_zero] using hpt.add hnt

lemma CurvatureDimension.cheegerHeat_bounded_pairing_continuousOn {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hi : Integrable u m)
    {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, ‖φ x‖ ≤ B) : ContinuousOn (fun t => ∫ x,cheegerHeat h t u x*φ x ∂m) (Ici 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_iff_continuousAt.mpr
  intro t
  have hL1 := hcd.cheegerHeat_L1_tendsto hN hfull hfin o h u hi
    (fun i : Ici (0:ℝ) => i.property) t.property (continuous_subtype_val.tendsto t)
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  have hb (i : Ici (0:ℝ)) : ‖(∫ x,cheegerHeat h i u x*φ x ∂m)-(∫ x,cheegerHeat h t u x*φ x ∂m)‖ ≤
      B*(∫ x,‖cheegerHeat h i u x-cheegerHeat h t u x‖ ∂m) := by
    have h1 := (cheegerHeat_integrable hfin o h u hi i.property).1
    have h2 := (cheegerHeat_integrable hfin o h u hi t.property).1
    rw [← integral_sub (h1.mul_bdd hφ hB) (h2.mul_bdd hφ hB)]
    have H := norm_integral_le_of_norm_le (f := fun x => cheegerHeat h i u x*φ x-cheegerHeat h t u x*φ x) ((h1.sub h2).norm.const_mul B) (by
      filter_upwards [hB] with x hx
      dsimp only [Pi.sub_apply]
      rw [← sub_mul,norm_mul]
      simpa only [mul_comm B] using mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    simpa only [integral_const_mul,Pi.sub_apply] using H
  apply squeeze_zero_norm hb
  simpa only [mul_zero] using hL1.const_mul B
end WeakHessian

end
end InlinedFile0

end OAI
