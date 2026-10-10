import Mathlib
import OAI.Geometry.WeakHessian.Transport.LocalSlopeCompContraction
import OAI.Geometry.WeakHessian.Measure.LocalSlopeNotMem
import OAI.Geometry.WeakHessian.HeatFlow.ScaledResolventCfc

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

def cheegerHeat (h : QuadraticCheegerEnergy m) (t : ℝ) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  realHeat m (cheeger_closedQuadraticEnergy h).resolventLinear t

lemma cheegerHeat_zero (h : QuadraticCheegerEnergy m) : cheegerHeat h 0 = 1 :=
  realHeat_zero m (cheeger_closedQuadraticEnergy h).resolvent_positive

lemma cheegerHeat_add (h : QuadraticCheegerEnergy m) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    cheegerHeat h (t+s) = cheegerHeat h t * cheegerHeat h s := realHeat_add m _ ht hs

lemma cheegerHeat_contractive (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t)
    (u v : Lp ℝ 2 m) : dist (cheegerHeat h t u) (cheegerHeat h t v) ≤ dist u v :=
  realHeat_contractive m (cheeger_closedQuadraticEnergy h).resolvent_positive
    (cheeger_closedQuadraticEnergy h).resolvent_le_one ht u v

lemma cheegerHeat_symmetric (h : QuadraticCheegerEnergy m) (t : ℝ) :
    (cheegerHeat h t).toLinearMap.IsSymmetric := realHeat_symmetric m _ t

lemma cheegerHeat_strong_zero [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [IsLocallyFiniteMeasure m] (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) :
    Tendsto (fun t : ℝ => cheegerHeat h t u) (𝓝[≥] (0:ℝ)) (𝓝 u) :=
  realHeat_strong_zero m (cheeger_closedQuadraticEnergy h).resolvent_positive
    (cheeger_closedQuadraticEnergy h).resolvent_le_one
    ((cheeger_closedQuadraticEnergy h).resolvent_injective (cheeger_domain_dense h)) u


lemma cheegerHeat_normal_fixed (h : QuadraticCheegerEnergy m)
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0) (u : Lp ℝ 2 m)
    (hu : hη.compLp hη0 u = u) {t : ℝ} (ht : 0 ≤ t) :
    hη.compLp hη0 (cheegerHeat h t u) = cheegerHeat h t u := by
  apply (cheeger_closedQuadraticEnergy h).heat_normal_fixed m hη hη0 _ u hu ht
  intro f
  rw [cheegerEnergy_congr_ae (hη.coeFn_compLp hη0 f)]
  exact cheegerEnergy_normalContraction hη hη0 f

lemma cheegerHeat_nonneg (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, 0 ≤ u x) :
    ∀ᵐ x ∂m, 0 ≤ (cheegerHeat h t) u x := by
  let η : ℝ → ℝ := fun r => max r 0
  have hη : LipschitzWith 1 η := lipschitzWith_posPart
  have hη0 : η 0 = 0 := max_self _
  have hufix : hη.compLp hη0 u = u := by
    apply Lp.ext
    filter_upwards [hη.coeFn_compLp hη0 u, hu] with x hx hu
    simpa only [Function.comp_apply, η, max_eq_left hu] using hx
  have hfix := cheegerHeat_normal_fixed h hη hη0 u hufix ht
  filter_upwards [hη.coeFn_compLp hη0 ((cheegerHeat h t) u)] with x hx
  rw [hfix] at hx
  change (cheegerHeat h t) u x =
    max ((cheegerHeat h t) u x) 0 at hx
  rw [hx]
  exact le_max_right _ _

lemma cheegerHeat_order (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t) (u v : Lp ℝ 2 m)
    (huv : ∀ᵐ x ∂m, u x ≤ v x) :
    ∀ᵐ x ∂m, (cheegerHeat h t) u x ≤
      (cheegerHeat h t) v x := by
  have hsub : ∀ᵐ x ∂m, 0 ≤ (v-u) x := by
    filter_upwards [huv, Lp.coeFn_sub v u] with x hx hs
    simpa only [hs, Pi.sub_apply, sub_nonneg] using hx
  have hnon := cheegerHeat_nonneg h ht (v-u) hsub
  have hlin : (cheegerHeat h t) (v-u) =
      (cheegerHeat h t) v-(cheegerHeat h t) u :=
    (cheegerHeat h t).map_sub v u
  rw [hlin] at hnon
  filter_upwards [hnon, Lp.coeFn_sub ((cheegerHeat h t) v)
    ((cheegerHeat h t) u)] with x hn hs
  simpa only [hs, Pi.sub_apply, sub_nonneg] using hn


lemma cheegerHeat_interval (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t)
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, u x ∈ Icc a b) :
    ∀ᵐ x ∂m, cheegerHeat h t u x ∈ Icc a b := by
  let η : ℝ → ℝ := fun r => max a (min r b)
  have hη : LipschitzWith 1 η := (LipschitzWith.id.min_const b).const_max a
  have hη0 : η 0 = 0 := by simp only [η, min_eq_left hb, max_eq_right ha]
  have hfixu : hη.compLp hη0 u = u := by
    apply Lp.ext
    filter_upwards [hη.coeFn_compLp hη0 u, hu] with x hx hu
    simpa only [Function.comp_apply, η, min_eq_left hu.2, max_eq_right hu.1] using hx
  have hfix := cheegerHeat_normal_fixed h hη hη0 u hfixu ht
  filter_upwards [hη.coeFn_compLp hη0 (cheegerHeat h t u)] with x hx
  rw [hfix] at hx
  change cheegerHeat h t u x = max a (min (cheegerHeat h t u x) b) at hx
  rw [hx]
  exact ⟨le_max_left _ _, max_le (ha.trans hb) (min_le_right _ _)⟩

lemma cheegerHeat_bounded (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t)
    {B : ℝ} (hB : 0 ≤ B) (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m, |u x| ≤ B) :
    ∀ᵐ x ∂m, |cheegerHeat h t u x| ≤ B := by
  have hu' : ∀ᵐ x ∂m, u x ∈ Icc (-B) B := hu.mono fun _ hx => abs_le.mp hx
  exact (cheegerHeat_interval h ht (neg_nonpos.mpr hB) hB u hu').mono fun _ hx => abs_le.mpr hx

end WeakHessian

end

end OAI
