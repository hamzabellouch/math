import Mathlib
import OAI.Analysis.SymmetricDomains.FieldSecondJet

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set MeasureTheory
open scoped ENNReal NNReal

theorem local_haar_cross_multiply
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν]
    [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (S : Set G)
    (hν : ∀ (g : G) (A B : Set G), MeasurableSet A → A ⊆ S →
      MeasurableSet B → B ⊆ S →
      ν (B ∩ (fun y => g⁻¹*y) ⁻¹' A) = ν (A ∩ (fun x => g*x) ⁻¹' B))
    {A B : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hB : MeasurableSet B) (hBS : B ⊆ S) :
    μ A * ν B = μ B * ν A := by
  classical
  let a : G → ℝ≥0∞ := A.indicator 1
  let b : G → ℝ≥0∞ := B.indicator 1
  have ha : Measurable a := measurable_const.indicator hA
  have hb : Measurable b := measurable_const.indicator hB
  have hleft (y : G) : (∫⁻ g, a (g⁻¹*y) ∂μ) = μ A := by
    rw [lintegral_inv_eq_self (fun g => a (g*y)),lintegral_mul_right_eq_self]
    exact lintegral_indicator_one hA
  have hright (x : G) : (∫⁻ g, b (g*x) ∂μ) = μ B := by
    rw [lintegral_mul_right_eq_self]
    exact lintegral_indicator_one hB
  have hsetL (g : G) : (∫⁻ y, b y*a (g⁻¹*y) ∂ν) =
      ν (B ∩ (fun y => g⁻¹*y) ⁻¹' A) := by
    have he : (fun y => b y*a (g⁻¹*y)) =
        (B ∩ (fun y => g⁻¹*y) ⁻¹' A).indicator 1 := by
      funext y
      by_cases hy : y∈B <;> by_cases hg : g⁻¹*y∈A <;> simp [a,b,hy,hg]
    rw [he]
    exact lintegral_indicator_one (hB.inter (hA.preimage (measurable_const.mul measurable_id)))
  have hsetR (g : G) : (∫⁻ x, a x*b (g*x) ∂ν) =
      ν (A ∩ (fun x => g*x) ⁻¹' B) := by
    have he : (fun x => a x*b (g*x)) =
        (A ∩ (fun x => g*x) ⁻¹' B).indicator 1 := by
      funext x
      by_cases hx : x∈A <;> by_cases hg : g*x∈B <;> simp [a,b,hx,hg]
    rw [he]
    exact lintegral_indicator_one (hA.inter (hB.preimage (measurable_const.mul measurable_id)))
  calc
    μ A * ν B = ∫⁻ y, b y * (∫⁻ g, a (g⁻¹*y) ∂μ) ∂ν := by
      simp_rw [hleft]
      rw [lintegral_mul_const _ hb,show (∫⁻ y, b y ∂ν)=ν B from lintegral_indicator_one hB,mul_comm]
    _ = ∫⁻ y, ∫⁻ g, b y*a (g⁻¹*y) ∂μ ∂ν := by
      congr with y
      exact (lintegral_const_mul _ ((ha.comp (measurable_inv.mul_const y)))).symm
    _ = ∫⁻ g, ∫⁻ y, b y*a (g⁻¹*y) ∂ν ∂μ := by
      apply lintegral_lintegral_swap
      exact ((hb.comp measurable_fst).mul
        (ha.comp (measurable_snd.inv.mul measurable_fst))).aemeasurable
    _ = ∫⁻ g, ∫⁻ x, a x*b (g*x) ∂ν ∂μ := by
      apply lintegral_congr
      intro g
      rw [hsetL,hsetR]
      exact hν g A B hA hAS hB hBS
    _ = ∫⁻ x, ∫⁻ g, a x*b (g*x) ∂μ ∂ν := by
      apply lintegral_lintegral_swap
      exact ((ha.comp measurable_snd).mul
        (hb.comp (measurable_fst.mul measurable_snd))).aemeasurable
    _ = ∫⁻ x, a x * (∫⁻ g, b (g*x) ∂μ) ∂ν := by
      congr with x
      exact lintegral_const_mul _ (hb.comp (measurable_id.mul_const x))
    _ = μ B * ν A := by
      simp_rw [hright]
      rw [lintegral_mul_const _ ha,show (∫⁻ x, a x ∂ν)=ν A from lintegral_indicator_one hA,mul_comm]

theorem local_haar_equal_mass
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν]
    [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (S : Set G)
    (hν : ∀ (g : G) (A B : Set G), MeasurableSet A → A ⊆ S →
      MeasurableSet B → B ⊆ S →
      ν (B ∩ (fun y => g⁻¹*y) ⁻¹' A) = ν (A ∩ (fun x => g*x) ⁻¹' B))
    {B : Set G} (hB : MeasurableSet B) (hBS : B ⊆ S)
    (hB0 : μ B ≠ 0) (hBtop : μ B ≠ (∞ : ℝ≥0∞))
    {A A' : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hA' : MeasurableSet A') (hA'S : A' ⊆ S) (h : μ A=μ A') :
    ν A=ν A' := by
  apply (ENNReal.mul_right_inj hB0 hBtop).mp
  rw [← local_haar_cross_multiply μ ν S hν hA hAS hB hBS,
    ← local_haar_cross_multiply μ ν S hν hA' hA'S hB hBS,h]

end Release061

end

end OAI
