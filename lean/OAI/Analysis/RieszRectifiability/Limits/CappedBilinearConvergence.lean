import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.SignedKernelConvergence
import OAI.Analysis.RieszRectifiability.Kernel.CappedBilinearKernel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem antisymmetric_kernel_pairing {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : X → ℝ) (hw : Integrable w μ)
    (F : X × X → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ q, |F q| ≤ B)
    (hanti : ∀ q, F q.swap = -F q) :
    Integrable (fun q : X × X => (w q.1 - w q.2) * F q) (μ.prod μ) ∧
      (∫ q : X × X, (w q.1 - w q.2) * F q ∂μ.prod μ) =
        2 * ∫ q : X × X, w q.1 * F q ∂μ.prod μ := by
  have hi := integrable_weighted_product_kernel μ μ w hw F hF B hB
  have hswap : Integrable (fun q : X × X => w q.2 * F q.swap) (μ.prod μ) := hi.swap
  have heq : (fun q : X × X => (w q.1 - w q.2) * F q) =
      fun q => w q.1 * F q + w q.2 * F q.swap := by
    funext q
    rw [hanti q]
    ring
  refine ⟨heq ▸ hi.add hswap, ?_⟩
  rw [heq, integral_add hi hswap]
  have hswapInt : (∫ q : X × X, w q.2 * F q.swap ∂μ.prod μ) =
      ∫ q : X × X, w q.1 * F q ∂μ.prod μ :=
    integral_prod_swap (fun q : X × X => w q.1 * F q)
  rw [hswapInt]
  ring

theorem capped_bilinear_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 (μ j)) (hv : MemLp v 2 ν)
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set (Ambient d))
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂μ j, y ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ y ∂ν, y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Ambient d) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(μ j).restrict (s k i), dist y (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ y ∂ν.restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (M : ℝ) (hM : 0 ≤ M)
    (htotal : ∀ᶠ j in atTop, (μ j).real univ ≤ M)
    (hsecond : ∀ᶠ j in atTop, (∫ x, w j x ^ 2 ∂μ j) ≤ M)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (D : ℝ≥0), LipschitzWith D ψ →
      MemLp ψ 2 ν → (∀ j, MemLp ψ 2 (μ j)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, v x * ψ x ∂ν)))
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      (w j q.1 - w j q.2) * cappedTestKernel m ε φ q ∂(μ j).prod (μ j)) atTop
      (𝓝 (∫ q : Ambient d × Ambient d,
        (v q.1 - v q.2) * cappedTestKernel m ε φ q ∂ν.prod ν)) := by
  let F := cappedTestKernel m ε φ
  let D := (2 * B) * Real.toNNReal (2 * (m + 1 : ℝ) * (ε ^ (m + 2))⁻¹) +
    (L + L) * Real.toNNReal ((ε ^ (m + 1))⁻¹)
  let Q := (2 * (B : ℝ)) * (ε ^ (m + 1))⁻¹
  have hF : LipschitzWith D F := cappedTestKernel_lipschitz m ε hε φ L B hφ hB
  have hQ : ∀ q, |F q| ≤ Q := cappedTestKernel_bound m ε hε φ B hB
  have hwI : ∀ j, Integrable (w j) (μ j) := fun j => (hw j).integrable (by norm_num)
  have hvI : Integrable v ν := hv.integrable (by norm_num)
  have hweight : ∀ᶠ j in atTop, (∫ x, |w j x| ∂μ j) ≤ M := by
    filter_upwards [htotal, hsecond] with j hjmass hjsecond
    simpa only [one_pow, mul_one] using! integral_abs_le_of_mass_second_moment
      (μ j) (w j) (hw j) M 1 hM (by norm_num) hjmass
        (by simpa only [one_pow, mul_one] using! hjsecond)
  have hslices : ∀ y, Tendsto (fun j => ∫ x, w j x * F (x, y) ∂μ j) atTop
      (𝓝 (∫ x, v x * F (x, y) ∂ν)) := by
    intro y
    have hLip : LipschitzWith D (fun x => F (x, y)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x x'
      simpa only [dist_prod_same_right] using! hF.dist_le_mul (x, y) (x', y)
    have hmem (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] : MemLp (fun x => F (x, y)) 2 ρ :=
      MemLp.of_bound hLip.continuous.measurable.aestronglyMeasurable Q
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hQ (x, y))
    exact hmoment (fun x => F (x, y)) D hLip (hmem ν) (fun j => hmem (μ j))
  have hprod := weighted_product_kernel_tendsto μ ν μ ν w v hwI hvI
    ι s hs hd hcover hcoverν z r hr hrzero hcell hcellν hmass M M hM hM
    hweight htotal F D hF Q hQ hslices
  have hanti : ∀ q, F q.swap = -F q := cappedTestKernel_antisymm m ε φ
  have heq (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (u : Ambient d → ℝ)
      (hu : Integrable u ρ) :
      (∫ q : Ambient d × Ambient d, (u q.1 - u q.2) * F q ∂ρ.prod ρ) =
        2 * ∫ q : Ambient d × Ambient d, u q.1 * F q ∂ρ.prod ρ :=
    (antisymmetric_kernel_pairing ρ u hu F hF.continuous.measurable Q hQ hanti).2
  have heqj : ∀ j, (∫ q : Ambient d × Ambient d,
      (w j q.1 - w j q.2) * cappedTestKernel m ε φ q ∂(μ j).prod (μ j)) =
        2 * ∫ q : Ambient d × Ambient d, w j q.1 * F q ∂(μ j).prod (μ j) :=
    fun j => heq (μ j) (w j) (hwI j)
  have heqν := heq ν v hvI
  change Tendsto (fun j => ∫ q : Ambient d × Ambient d,
    (w j q.1 - w j q.2) * F q ∂(μ j).prod (μ j)) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, (v q.1 - v q.2) * F q ∂ν.prod ν))
  rw [heqν]
  exact (hprod.const_mul 2).congr' (Filter.Eventually.of_forall fun j => (heqj j).symm)

end

end RieszRectifiability

end OAI
