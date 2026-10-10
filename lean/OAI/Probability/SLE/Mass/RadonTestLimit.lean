import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.MetricSpace.Sequences

namespace OAI

/-! Deterministic reconstruction in `mass:construction`. A countable
family locally dense in compactly supported continuous functions,
including nonnegative exhaustion cutoffs, determines one Radon limit. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- A countable determining family with explicit support control.
Density is in the uniform norm within each compact exhaustion set. -/
structure LocalTestFamily (X : Type*) [TopologicalSpace X] where
  compactSet : ℕ → Set X
  isCompact : ∀ n, IsCompact (compactSet n)
  exhaustive : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ compactSet n
  test : ℕ → C_c(X, ℝ)
  cutoffIndex : ℕ → ℕ
  cutoff_nonneg : ∀ n x, 0 ≤ test (cutoffIndex n) x
  cutoff_one_le : ∀ n x, x ∈ compactSet n → 1 ≤ test (cutoffIndex n) x
  dense : ∀ n (f : C_c(X, ℝ)), tsupport f ⊆ compactSet n →
    ∀ ε : ℝ, 0 < ε → ∃ j, tsupport (test j) ⊆ compactSet n ∧
      ∀ x, |f x-test j x| ≤ ε

omit [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma LocalTestFamily.weighted_approximation (D : LocalTestFamily X) (f : C_c(X, ℝ)) :
    ∃ k, (∀ x, 0 ≤ D.test k x) ∧ ∀ ε : ℝ, 0 < ε →
      ∃ j, ∀ x, |f x-D.test j x| ≤ ε * D.test k x := by
  obtain ⟨n,hn⟩ := D.exhaustive (tsupport f) f.hasCompactSupport
  refine ⟨D.cutoffIndex n,D.cutoff_nonneg n,fun ε hε => ?_⟩
  obtain ⟨j,hj,happrox⟩ := D.dense n f hn ε hε
  refine ⟨j,fun x => ?_⟩
  by_cases hx : x ∈ D.compactSet n
  · exact (happrox x).trans (le_mul_of_one_le_right hε.le (D.cutoff_one_le n x hx))
  · have hfx : f x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hn h))
    have hjx : D.test j x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hj h))
    rw [hfx,hjx,sub_self,abs_zero]
    exact mul_nonneg hε.le (D.cutoff_nonneg n x)

omit [T2Space X] [LocallyCompactSpace X] in
lemma integral_sub_le_cutoff (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f g ψ : C_c(X, ℝ)) (ε : ℝ)
    (h : ∀ x, |f x-g x| ≤ ε*ψ x) :
    |(∫ x, f x ∂μ)-(∫ x, g x ∂μ)| ≤ ε*(∫ x, ψ x ∂μ) := by
  rw [← integral_sub f.integrable g.integrable]
  have hh := norm_integral_le_of_norm_le (f := fun x => f x-g x) (ψ.integrable.const_mul ε)
    (ae_of_all μ (fun x => by simpa only [Real.norm_eq_abs] using h x))
  simpa only [Real.norm_eq_abs,integral_const_mul] using hh

omit [T2Space X] [LocallyCompactSpace X] in
/-- Compactly supported integrals are Cauchy once the countable tests
converge. Cutoff convergence supplies the uniform local mass bounds. -/
theorem LocalTestFamily.integrals_cauchy (D : LocalTestFamily X)
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasureOnCompacts (μ n)]
    (htest : ∀ j, ∃ a : ℝ, Tendsto (fun n => ∫ x, D.test j x ∂μ n) atTop (𝓝 a))
    (f : C_c(X, ℝ)) : CauchySeq (fun n => ∫ x, f x ∂μ n) := by
  obtain ⟨k,_,hk⟩ := D.weighted_approximation f
  obtain ⟨a,ha⟩ := htest k
  obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto _ ha).exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ (mem_range_self 0))
  have hB' (n : ℕ) : (∫ x, D.test k x ∂μ n) ≤ B :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB _ (mem_range_self n))
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ : ℝ := ε/(4*(B+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδB : δ*B < ε/4 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div,div_lt_div_iff₀ (by positivity) (by norm_num : (0:ℝ)<4)]
    nlinarith
  obtain ⟨j,hj⟩ := hk δ hδ
  obtain ⟨a,ha⟩ := htest j
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp ha.cauchySeq (ε/2) (by positivity)
  have herror (n : ℕ) : dist (∫ x, f x ∂μ n) (∫ x, D.test j x ∂μ n) ≤ δ*B := by
    rw [Real.dist_eq]
    exact (integral_sub_le_cutoff (μ n) f (D.test j) (D.test k) δ hj).trans
      (mul_le_mul_of_nonneg_left (hB' n) hδ.le)
  refine ⟨N,fun n hn m hm => ?_⟩
  have hmid := hN n hn m hm
  have htri := dist_triangle (∫ x, f x ∂μ n) (∫ x, D.test j x ∂μ n) (∫ x, f x ∂μ m)
  have htri' := dist_triangle (∫ x, D.test j x ∂μ n) (∫ x, D.test j x ∂μ m) (∫ x, f x ∂μ m)
  have hright : dist (∫ x, D.test j x ∂μ m) (∫ x, f x ∂μ m) ≤ δ*B := by
    rw [dist_comm]
    exact herror m
  have hleft := herror n
  linarith

/-- Positive limits of compact continuous tests are represented by one
locally finite regular measure. -/
theorem radon_limit_of_all_test_limits (μ : ℕ → Measure X)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)]
    (hlimit : ∀ f : C_c(X, ℝ), ∃ a : ℝ,
      Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 a)) :
    ∃ ν : Measure X, ν.Regular ∧ IsFiniteMeasureOnCompacts ν ∧
      ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  choose L hL using hlimit
  let I (n : ℕ) : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    CompactlySupportedContinuousMap.integralPositiveLinearMap (μ n)
  have hI (f : C_c(X, ℝ)) : Tendsto (fun n => I n f) atTop (𝓝 (L f)) := hL f
  have hadd (f g : C_c(X, ℝ)) : L (f+g) = L f+L g := by
    apply tendsto_nhds_unique (hI (f+g))
    simpa only [map_add] using (hI f).add (hI g)
  have hsmul (c : ℝ) (f : C_c(X, ℝ)) : L (c • f) = c • L f := by
    apply tendsto_nhds_unique (hI (c • f))
    simpa only [map_smul] using tendsto_const_nhds.smul (hI f)
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := L
      map_add' := hadd
      map_smul' := hsmul
      monotone' := fun f g hfg => le_of_tendsto_of_tendsto' (hI f) (hI g)
        (fun n => (I n).monotone hfg) }
  refine ⟨RealRMK.rieszMeasure Λ,inferInstance,inferInstance,fun f => ?_⟩
  rw [RealRMK.integral_rieszMeasure]
  exact hL f

/-- Reconstruction from a single countable locally determining family. -/
theorem LocalTestFamily.exists_radon_limit (D : LocalTestFamily X)
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasureOnCompacts (μ n)]
    (htest : ∀ j, ∃ a : ℝ, Tendsto (fun n => ∫ x, D.test j x ∂μ n) atTop (𝓝 a)) :
    ∃ ν : Measure X, ν.Regular ∧ IsFiniteMeasureOnCompacts ν ∧
      ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  apply radon_limit_of_all_test_limits μ
  intro f
  exact cauchySeq_tendsto_of_complete (D.integrals_cauchy μ htest f)

end SLEExactGauge

end

end OAI
