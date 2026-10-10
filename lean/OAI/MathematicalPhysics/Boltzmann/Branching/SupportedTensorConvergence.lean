import OAI.MathematicalPhysics.Boltzmann.Branching.CompactParameterConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UrysohnsLemma

namespace OAI

section

/-! # Uniform approximation by products of compactly supported velocity tests -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

inductive IsSupportedTensorSum : C(X × Y, ℝ) → Prop
  | zero : IsSupportedTensorSum 0
  | tensor (f : C(X, ℝ)) (g : C(Y, ℝ))
      (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
      IsSupportedTensorSum (tensorTest f g)
  | add {f g} : IsSupportedTensorSum f → IsSupportedTensorSum g → IsSupportedTensorSum (f+g)
  | smul (r : ℝ) {f} : IsSupportedTensorSum f → IsSupportedTensorSum (r • f)

theorem tensorTest_tsupport_subset (f : C(X, ℝ)) (g : C(Y, ℝ)) :
    tsupport (tensorTest f g) ⊆ tsupport f ×ˢ tsupport g := by
  apply closure_minimal _ ((isClosed_tsupport f).prod (isClosed_tsupport g))
  intro p hp
  have hn : f p.1*g p.2 ≠ 0 := hp
  exact ⟨subset_closure (left_ne_zero_of_mul hn),subset_closure (right_ne_zero_of_mul hn)⟩

theorem tensorTest_hasCompactSupport {f : C(X, ℝ)} {g : C(Y, ℝ)}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (tensorTest f g) :=
  (hf.prod hg).of_isClosed_subset (isClosed_tsupport _) (tensorTest_tsupport_subset f g)

theorem IsSupportedTensorSum.hasCompactSupport {f : C(X × Y, ℝ)} (hf : IsSupportedTensorSum f) :
    HasCompactSupport f := by
  induction hf with
  | zero => simp [HasCompactSupport]
  | tensor f g hf hg => exact tensorTest_hasCompactSupport hf hg
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | smul r _ ih => exact ih.smul_left

theorem IsTensorSum.cutoff {f : C(X × Y, ℝ)} (hf : IsTensorSum f)
    {β : C(X, ℝ)} {γ : C(Y, ℝ)} (hβ : HasCompactSupport β) (hγ : HasCompactSupport γ) :
    IsSupportedTensorSum (tensorTest β γ*f) := by
  induction hf with
  | zero => simpa only [mul_zero] using
      (IsSupportedTensorSum.zero : IsSupportedTensorSum (0 : C(X × Y, ℝ)))
  | tensor a b =>
    have he : tensorTest β γ*tensorTest a b = tensorTest (β*a) (γ*b) := by
      ext p
      change (β p.1*γ p.2)*(a p.1*b p.2) = (β p.1*a p.1)*(γ p.2*b p.2)
      ring
    rw [he]
    exact IsSupportedTensorSum.tensor _ _ hβ.mul_right hγ.mul_right
  | add _ _ ih₁ ih₂ => simpa only [mul_add] using IsSupportedTensorSum.add ih₁ ih₂
  | smul r _ ih => simpa only [mul_smul_comm] using IsSupportedTensorSum.smul r ih

theorem exists_supported_tensorSum_uniform [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (f : C(X × Y, ℝ)) (hf : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(X × Y, ℝ), IsSupportedTensorSum g ∧ ∀ p, |g p-f p| < ε := by
  obtain ⟨β,hβone,hβc,_hβs,hβ⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (hf.image continuous_fst) isOpen_univ (subset_univ _)
  obtain ⟨γ,hγone,hγc,_hγs,hγ⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (hf.image continuous_snd) isOpen_univ (subset_univ _)
  have hcut (p : X × Y) : tensorTest β γ p*f p = f p := by
    by_cases hp : f p = 0
    · simp only [hp,mul_zero]
    · have hpt : p ∈ tsupport f := subset_closure hp
      have hb : β p.1 = 1 := hβone (mem_image_of_mem Prod.fst hpt)
      have hg : γ p.2 = 1 := hγone (mem_image_of_mem Prod.snd hpt)
      simp only [tensorTest,ContinuousMap.coe_mk,hb,hg,one_mul]
  obtain ⟨g,hg,happrox⟩ := exists_tensorSum_near_compact f (hβc.prod hγc) hε
  refine ⟨tensorTest β γ*g,hg.cutoff hβc hγc,fun p => ?_⟩
  change |tensorTest β γ p*g p-f p| < ε
  rw [← hcut p,← mul_sub,abs_mul]
  by_cases hp : p ∈ tsupport β ×ˢ tsupport γ
  · have hb : |tensorTest β γ p| ≤ 1 := by
      change |β p.1*γ p.2| ≤ 1
      rw [abs_of_nonneg (mul_nonneg (hβ _).1 (hγ _).1)]
      simpa only [one_mul] using mul_le_mul (hβ p.1).2 (hγ p.2).2 (hγ _).1 zero_le_one
    exact (mul_le_of_le_one_left (abs_nonneg _) hb).trans_lt (happrox p hp)
  · have hz : tensorTest β γ p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (tensorTest_tsupport_subset β γ h))
    simpa only [hz,abs_zero,zero_mul] using hε

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Full-space mixed measures from compactly supported separated tests -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [SecondCountableTopology Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

private theorem supported_integrable (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (f : C(X × Y, ℝ)) (hf : HasCompactSupport f) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport hf

theorem IsSupportedTensorSum.integral_tendsto
    {μ : ℕ → Measure (X × Y)} {ν : Measure (X × Y)}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    (h : ∀ f : C(X, ℝ), ∀ g : C(Y, ℝ), HasCompactSupport f → HasCompactSupport g →
      Tendsto (fun n => ∫ p, f p.1*g p.2 ∂μ n) atTop
        (𝓝 (∫ p, f p.1*g p.2 ∂ν)))
    {k : C(X × Y, ℝ)} (hk : IsSupportedTensorSum k) :
    Tendsto (fun n => ∫ p, k p ∂μ n) atTop (𝓝 (∫ p, k p ∂ν)) := by
  induction hk with
  | zero => simpa only [ContinuousMap.zero_apply,integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | tensor f g hf hg => exact h f g hf hg
  | @add f g hf hg ih₁ ih₂ =>
    simpa only [ContinuousMap.add_apply,
      integral_add (supported_integrable _ f hf.hasCompactSupport)
        (supported_integrable _ g hg.hasCompactSupport)] using ih₁.add ih₂
  | smul r _ ih =>
    simpa only [ContinuousMap.smul_apply,smul_eq_mul,integral_const_mul] using ih.const_mul r

private theorem supported_integral_error (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (f g : C(X × Y, ℝ)) (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    {δ : ℝ} (hδ : ∀ p, |f p-g p| ≤ δ) :
    |(∫ p, f p ∂μ)-(∫ p, g p ∂μ)| ≤ δ*μ.real univ := by
  rw [← integral_sub (supported_integrable _ f hf) (supported_integrable _ g hg),← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const (ae_of_all _ (fun p => by
    simpa only [Real.norm_eq_abs] using hδ p))

theorem supported_integral_tendsto_of_tensor_tests
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    {μ : ℕ → Measure (X × Y)} {ν : Measure (X × Y)}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    {C : ℝ} (hC : 0 ≤ C) (hμ : ∀ᶠ n in atTop, (μ n).real univ ≤ C)
    (h : ∀ f : C(X, ℝ), ∀ g : C(Y, ℝ), HasCompactSupport f → HasCompactSupport g →
      Tendsto (fun n => ∫ p, f p.1*g p.2 ∂μ n) atTop
        (𝓝 (∫ p, f p.1*g p.2 ∂ν)))
    (f : C(X × Y, ℝ)) (hf : HasCompactSupport f) :
    Tendsto (fun n => ∫ p, f p ∂μ n) atTop (𝓝 (∫ p, f p ∂ν)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let D := ν.real univ
  have hD : 0 ≤ D := measureReal_nonneg
  let δ := ε/(3*(C+D+1))
  have hden : 0 < 3*(C+D+1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ*(3*(C+D+1)) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨g,hg,happrox⟩ := exists_supported_tensorSum_uniform f hf hδ
  have hfg (p) : |f p-g p| ≤ δ := by rw [abs_sub_comm]; exact (happrox p).le
  have hgf (p) : |g p-f p| ≤ δ := (happrox p).le
  have hmid := Metric.tendsto_nhds.mp (hg.integral_tendsto h) (ε/3) (by positivity)
  filter_upwards [hμ,hmid] with n hn hgn
  rw [Real.dist_eq] at hgn ⊢
  have hleft := (supported_integral_error (μ n) f g hf hg.hasCompactSupport hfg).trans
    (mul_le_mul_of_nonneg_left hn hδ.le)
  have hright := supported_integral_error ν g f hg.hasCompactSupport hf hgf
  have htri := (abs_sub_le (∫ p, f p ∂μ n) (∫ p, g p ∂μ n) (∫ p, f p ∂ν)).trans
    (add_le_add le_rfl (abs_sub_le (∫ p, g p ∂μ n) (∫ p, g p ∂ν) (∫ p, f p ∂ν)))
  change |(∫ p, g p ∂ν)-(∫ p, f p ∂ν)| ≤ δ*D at hright
  nlinarith

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
