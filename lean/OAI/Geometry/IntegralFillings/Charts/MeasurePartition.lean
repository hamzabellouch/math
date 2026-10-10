import Mathlib
import OAI.Geometry.IntegralFillings.Model
import OAI.Geometry.IntegralFillings.Charts.DensityPush
import OAI.Geometry.IntegralFillings.Geometry.Polarization
import OAI.Geometry.IntegralFillings.Geometry.MatrixRows

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma densityPush_mono_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {φ : α → β} (hφ : Measurable φ) {ρ σ : α → ℝ}
    (h : ρ ≤ᵐ[μ] σ) : densityPush μ φ ρ ≤ densityPush μ φ σ := by
  rw [densityPush_eq_map μ hφ, densityPush_eq_map μ hφ]
  apply Measure.map_mono _ hφ
  exact withDensity_mono (h.mono fun _ hx => ENNReal.ofReal_le_ofReal hx)

lemma densityPush_const_mul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (φ : α → β) (ρ : α → ℝ) (c : ℝ≥0) :
    densityPush μ φ (fun z => (c : ℝ)*ρ z) = c • densityPush μ φ ρ := by
  by_cases hc : c = 0
  · subst c
    simp [densityPush]
  unfold densityPush
  have hfun : (fun z => ENNReal.ofReal ((c : ℝ)*ρ z)) =
      (c : ENNReal) • (fun z => ENNReal.ofReal (ρ z)) := by
    ext z
    simp only [Pi.smul_apply,smul_eq_mul,ENNReal.ofReal_mul c.coe_nonneg,ENNReal.ofReal_coe_nnreal]
  rw [hfun,withDensity_smul' _ _ ENNReal.coe_ne_top,
    aemeasurable_smul_measure_iff (ENNReal.coe_ne_zero.mpr hc)]
  by_cases hφ : AEMeasurable φ (μ.withDensity fun z => ENNReal.ofReal (ρ z))
  · simp only [ite_eq_left hφ]
    rw [Measure.map_smul _ hφ]
    rfl
  · simp only [ite_eq_right hφ, smul_zero]

lemma densityPush_sum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ι : Type*} (μ : ι → Measure α) {φ : α → β} (hφ : Measurable φ) (ρ : α → ℝ) :
    densityPush (Measure.sum μ) φ ρ = Measure.sum (fun i => densityPush (μ i) φ ρ) := by
  simp only [densityPush_eq_map _ hφ,withDensity_sum,Measure.map_sum hφ.aemeasurable]

lemma restrict_eq_sum_of_ae_partition {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {t : ℕ → Set α}
    (ht : ∀ i, MeasurableSet (t i)) (hts : ∀ i, t i ⊆ s)
    (hdisj : Pairwise (fun i j => Disjoint (t i) (t j))) (hnull : μ (s \ ⋃ i, t i) = 0) :
    μ.restrict s = Measure.sum (fun i => μ.restrict (t i)) := by
  have hsub : (⋃ i, t i) ⊆ s := iUnion_subset hts
  have heq : s =ᵐ[μ] ⋃ i, t i := ae_eq_set.mpr ⟨hnull,by simp only [sdiff_eq_empty.mpr hsub,measure_empty]⟩
  rw [Measure.restrict_congr_set heq,Measure.restrict_iUnion hdisj ht]

lemma densityPush_le_of_partition {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {φ : α → β} (hφ : Measurable φ) (ρ : α → ℝ)
    {s : Set α} {t : ℕ → Set α} (ht : ∀ i, MeasurableSet (t i)) (hts : ∀ i, t i ⊆ s)
    (hdisj : Pairwise (fun i j => Disjoint (t i) (t j))) (hnull : μ (s \ ⋃ i, t i) = 0)
    (him : ∀ i, MeasurableSet (φ '' t i)) (hinj : Set.InjOn φ s)
    (hbound : ∀ i, densityPush (μ.restrict (t i)) φ ρ ≤ ν.restrict (φ '' t i)) :
    densityPush (μ.restrict s) φ ρ ≤ ν := by
  rw [restrict_eq_sum_of_ae_partition ht hts hdisj hnull,densityPush_sum _ hφ]
  have hdisj' : Pairwise (fun i j => Disjoint (φ '' t i) (φ '' t j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hxi,rfl⟩ ⟨y,hyj,hxy⟩
    have hxy' : y = x := hinj (hts j hyj) (hts i hxi) hxy
    subst y
    exact Set.disjoint_left.mp (hdisj hij) hxi hyj
  calc
    _ ≤ Measure.sum (fun i => ν.restrict (φ '' t i)) := by
      apply Measure.le_iff.mpr
      intro u hu
      simp only [Measure.sum_apply _ hu]
      exact ENNReal.tsum_le_tsum (fun i => hbound i u)
    _ = ν.restrict (⋃ i, φ '' t i) := (Measure.restrict_iUnion hdisj' him).symm
    _ ≤ ν := Measure.restrict_le_self
end SharpIntegralFillings

namespace SharpIntegralFillings
open Matrix MeasureTheory Set Filter
open scoped MatrixOrder NNReal Topology

lemma sqrt_polarization_quadratic {k : ℕ} (p : Seminorm ℝ (Euc k))
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) (v : Fin k → ℝ) :
    Real.sqrt (v ⬝ᵥ (polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).mulVec v)
      = p (WithLp.toLp 2 v) := by
  have hrepr : (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.repr (WithLp.toLp 2 v) = v := by
    ext j
    simp
  have hquad := polarizationMatrix_quadratic (EuclideanSpace.basisFun (Fin k) ℝ).toBasis p hp hpara (WithLp.toLp 2 v)
  rw [hrepr] at hquad
  rw [hquad,Real.sqrt_sq (apply_nonneg _ _)]

lemma sqrt_det_polarization_le {k : ℕ} (p q : Seminorm ℝ (Euc k))
    (hp : ∀ v, p v = 0 ↔ v = 0) (hq : ∀ v, q v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2)
    (hqpara : ∀ u v, q (u+v)^2+q (u-v)^2 = 2*q u^2+2*q v^2)
    {L : ℝ} (hL : 0 ≤ L) (h : ∀ v, p v ≤ L*q v) :
    Real.sqrt (polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≤
    L^k * Real.sqrt (polarizationMatrix q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  apply sqrt_det_le_mul_sqrt_det _ _
    (polarizationMatrix_posDef _ p hp hpara).posSemidef
    (polarizationMatrix_posDef _ q hq hqpara) hL
  intro v
  simpa only [sqrt_polarization_quadratic p hp hpara,
    sqrt_polarization_quadratic q hq hqpara] using h (WithLp.toLp 2 v)

end SharpIntegralFillings
end

end OAI
