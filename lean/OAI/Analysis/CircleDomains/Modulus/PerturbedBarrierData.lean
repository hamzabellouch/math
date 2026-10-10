import OAI.Analysis.CircleDomains.Selection.ExtendedAtomicToll
import OAI.Analysis.CircleDomains.Sobolev.FiniteSphericalArea

namespace OAI

/-! An admissible extended coding metric supplies the actual positive
physical density, countable quotient tolls, and endpoint cost used by the
barrier theorem. No restriction on values on area-null sets is imposed. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem exists_perturbed_barrier_data
    {D : Type*} [TopologicalSpace D] [Countable D]
    [MeasurableSpace D] [BorelSpace D]
    [MeasurableSpace C(PathTime, Sphere)]
    (d : PathCodeData Sphere Sphere) (p : D → Sphere) (hp : Injective p)
    (c : D → ℝ≥0∞) (hc : (∑'s, c s ^ 2) < ∞)
    (ν : Measure Sphere) (τ : Measure LevelTuple)
    (h : PathCostSpace Sphere D → ℝ≥0∞) (hh : Measurable h)
    (hadm : CostAdmissible d p c ν h)
    (he : (∫⁻z, h z ^ 2 ∂pathCostReference sphericalArea c τ) < ∞)
    {ε : ℝ≥0∞} (hε : 0 < ε) (hεfin : ε ≠ ∞) :
    ∃(δ : ℝ≥0) (g : Sphere → ℝ≥0∞) (m : Sphere → ℝ≥0∞),
      0 < δ ∧ Measurable g ∧ (∀y, (δ : ℝ≥0∞) ≤ g y) ∧
      (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞ ∧ (∑'x, m x ^ 2) < ∞ ∧
      (∀x ∉ range p, m x = 0) ∧
      squareIntegralNorm sphericalArea g + countingSquareNorm m ≤
        2 * squareIntegralNorm (pathCostReference sphericalArea c τ) h + ε ∧
      ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) (ρ.val, θ) →
        1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
          preterminalToll ρ.val m := by
  obtain ⟨δ, hδ, hsize⟩ := exists_small_positive_perturbation sphericalArea c hc τ hh hε
  let g := perturbedPhysicalDensity h (δ : ℝ≥0∞)
  let a := perturbedAtomicToll h c (δ : ℝ≥0∞)
  let m := extendAtomicToll p a
  have hext : countingSquareNorm m = countingSquareNorm a := countingSquareNorm_extendAtomicToll hp a
  have hsize' : squareIntegralNorm sphericalArea g + countingSquareNorm m ≤
      2 * squareIntegralNorm (pathCostReference sphericalArea c τ) h + ε := by
    simpa only [hext] using hsize
  have hnorm : squareIntegralNorm sphericalArea g + countingSquareNorm m < ∞ :=
    lt_of_le_of_lt hsize' (ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) he.ne)),
        lt_top_iff_ne_top.mpr hεfin⟩)
  have hgfinite : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞ := by
    have hn := lt_of_le_of_lt le_self_add hnorm
    by_contra ht
    have ht' : (∫⁻y, g y ^ 2 ∂sphericalArea) = ∞ := top_unique (not_lt.mp ht)
    simp [squareIntegralNorm, ht'] at hn
  have hmfinite : (∑'x, m x ^ 2) < ∞ := by
    have hn := lt_of_le_of_lt le_add_self hnorm
    by_contra ht
    have ht' : (∑'x, m x ^ 2) = ∞ := top_unique (not_lt.mp ht)
    simp [countingSquareNorm, ht'] at hn
  exact ⟨δ, g, m, hδ, (hh.comp measurable_costPhysical).add_const _,
    (fun _ => le_add_self), hgfinite, hmfinite,
    (fun _ hx => extendAtomicToll_zero p a hx), hsize',
    fun ρ θ hΓ => perturbed_endpoint_cost_ge_one d p hp c ν h hh hadm
      (ENNReal.coe_pos.mpr hδ) ρ θ hΓ⟩

end CircleDomainRigidity

end

end OAI
