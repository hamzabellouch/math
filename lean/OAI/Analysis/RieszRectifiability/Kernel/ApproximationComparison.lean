import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FiniteStepLp

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem integral_sq_four_step_bound (μ : Measure X) (f p w q g : X → ℝ)
    (hf : MemLp f 2 μ) (hp : MemLp p 2 μ) (hw : MemLp w 2 μ)
    (hq : MemLp q 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, (f x - g x) ^ 2 ∂μ) ≤
      4 * ((∫ x, (f x - p x) ^ 2 ∂μ) + (∫ x, (p x - w x) ^ 2 ∂μ) +
        (∫ x, (w x - q x) ^ 2 ∂μ) + (∫ x, (q x - g x) ^ 2 ∂μ)) := by
  have hpoint (x : X) : (f x - g x) ^ 2 ≤
      4 * ((f x - p x) ^ 2 + (p x - w x) ^ 2 +
        (w x - q x) ^ 2 + (q x - g x) ^ 2) := by
    nlinarith [sq_nonneg ((f x - p x) - (p x - w x)),
      sq_nonneg ((w x - q x) - (q x - g x)),
      sq_nonneg ((f x - w x) - (w x - g x))]
  have hsum := (((hf.sub hp).integrable_sq.add (hp.sub hw).integrable_sq).add
    (hw.sub hq).integrable_sq).add (hq.sub hg).integrable_sq
  have h := integral_mono (hf.sub hg).integrable_sq (hsum.const_mul 4) hpoint
  have h1 := integral_add (hf.sub hp).integrable_sq (hp.sub hw).integrable_sq
  have h2 := integral_add ((hf.sub hp).integrable_sq.add (hp.sub hw).integrable_sq)
    (hw.sub hq).integrable_sq
  have h3 := integral_add
    (((hf.sub hp).integrable_sq.add (hp.sub hw).integrable_sq).add
      (hw.sub hq).integrable_sq) (hq.sub hg).integrable_sq
  simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
  simp only [integral_const_mul, Pi.add_apply, Pi.sub_apply] at h
  rw [h3, h2, h1] at h
  exact h

theorem fixed_pair_bound_of_approximations (μ : ℕ → Measure X) (ν : Measure X)
    (f g : X → ℝ) (p w q : ℕ → X → ℝ)
    (hf : ∀ j, MemLp f 2 (μ j)) (hg : ∀ j, MemLp g 2 (μ j))
    (hp : ∀ j, MemLp (p j) 2 (μ j)) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (hq : ∀ j, MemLp (q j) 2 (μ j)) (d e : ℝ)
    (hwp : ∀ᶠ j in atTop, (∫ x, (w j x - p j x) ^ 2 ∂μ j) ≤ d)
    (hwq : ∀ᶠ j in atTop, (∫ x, (w j x - q j x) ^ 2 ∂μ j) ≤ e)
    (hpf : Tendsto (fun j => ∫ x, (p j x - f x) ^ 2 ∂μ j) atTop (𝓝 0))
    (hqg : Tendsto (fun j => ∫ x, (q j x - g x) ^ 2 ∂μ j) atTop (𝓝 0))
    (hfg : Tendsto (fun j => ∫ x, (f x - g x) ^ 2 ∂μ j) atTop
      (𝓝 (∫ x, (f x - g x) ^ 2 ∂ν))) :
    (∫ x, (f x - g x) ^ 2 ∂ν) ≤ 4 * d + 4 * e := by
  have hlim : Tendsto (fun j => 4 *
      ((∫ x, (p j x - f x) ^ 2 ∂μ j) + d + e +
        (∫ x, (q j x - g x) ^ 2 ∂μ j))) atTop (𝓝 (4 * d + 4 * e)) := by
    simpa only [zero_add, add_zero, mul_add] using!
      (((hpf.add_const d).add_const e).add hqg).const_mul 4
  apply le_of_tendsto_of_tendsto hfg hlim
  filter_upwards [hwp, hwq] with j hjp hjq
  have h := integral_sq_four_step_bound (μ j) f (p j) (w j) (q j) g
    (hf j) (hp j) (hw j) (hq j) (hg j)
  have hfp : (fun x => (f x - p j x) ^ 2) = (fun x => (p j x - f x) ^ 2) := by
    funext x
    ring
  have hpw : (fun x => (p j x - w j x) ^ 2) = (fun x => (w j x - p j x) ^ 2) := by
    funext x
    ring
  rw [hfp, hpw] at h
  linarith

theorem exists_L2_limit_of_sq_distance_bound (ν : Measure X)
    (v : ℕ → Lp ℝ 2 ν) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ k l, dist (v k) (v l) ^ 2 ≤ 4 * δ k + 4 * δ l) :
    ∃ limit : Lp ℝ 2 ν, Tendsto v atTop (𝓝 limit) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hδ.eventually (gt_mem_nhds (show (0 : ℝ) < ε ^ 2 / 8 by positivity)))
  refine ⟨N, fun k hk l hl => ?_⟩
  have hb := hbound k l
  have hk' := hN k hk
  have hl' := hN l hl
  nlinarith [dist_nonneg (x := v k) (y := v l)]

end

end RieszRectifiability

end OAI
