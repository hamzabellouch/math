import OAI.Geometry.RCD.Sobolev.LipschitzMetricTransfer
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

namespace OAI

/-! # Uniform compactness of transferred Lipschitz data -/

open Set Filter
open scoped NNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

theorem exists_uniform_lipschitz_subsequence (f : ℕ → Y → ℝ) (L : ℝ≥0) (A : ℝ)
    (hl : ∀ k, LipschitzWith L (f k)) (hb : ∀ k y, |f k y| ≤ A) :
    ∃ (g : Y → ℝ) (a : ℕ → ℕ), StrictMono a ∧ LipschitzWith L g ∧
      (∀ y, |g y| ≤ A) ∧ TendstoUniformly (fun k => f (a k)) g atTop := by
  let F : ℕ → Y →ᵇ ℝ := fun k =>
    BoundedContinuousFunction.mkOfCompact ⟨f k,(hl k).continuous⟩
  have hc : IsCompact (closure (range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Icc (-A) A) isCompact_Icc (range F)
    · rintro q y ⟨k,rfl⟩
      exact abs_le.mp (hb k y)
    · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (L:ℝ)*r)
        (by simpa only [mul_zero] using
          (show Continuous (fun r : ℝ => (L:ℝ)*r) by fun_prop).tendsto (0:ℝ))
      rintro y z ⟨q,k,rfl⟩
      exact (hl k).dist_le_mul y z
  obtain ⟨g,_,a,ha,hlim⟩ := hc.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  have hp (y : Y) : Tendsto (fun k => f (a k) y) atTop (𝓝 (g y)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const y).continuous.tendsto g).comp hlim
  refine ⟨g,a,ha,?_,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    exact le_of_tendsto ((hp y).dist (hp z)) (Eventually.of_forall fun k =>
      (hl (a k)).dist_le_mul y z)
  · intro y
    exact le_of_tendsto (hp y).abs (Eventually.of_forall fun k => hb (a k) y)
  · exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim

/-- On a fixed compact region, the limit retains a global Lipschitz extension. -/
theorem exists_lipschitz_subsequence_on_compact {Z : Type*} [MetricSpace Z]
    {s : Set Z} (hs : IsCompact s) (f : ℕ → Z → ℝ) (L : ℝ≥0) (A : ℝ)
    (hl : ∀ k, LipschitzWith L (f k)) (hb : ∀ k z, z∈s → |f k z|≤A) :
    ∃ (g : Z → ℝ) (a : ℕ → ℕ), StrictMono a ∧ LipschitzWith L g ∧
      (∀ z∈s, |g z|≤A) ∧
      ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop, ∀ z∈s, |f (a k) z-g z|<ε := by
  classical
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  obtain ⟨G,a,ha,hG,hGb,hlim⟩ := exists_uniform_lipschitz_subsequence
    (fun k (z:s) => f k z) L A
    (fun k => by simpa only [mul_one,Function.comp_def] using (hl k).comp (LipschitzWith.subtype_val s)) (fun k z => hb k z z.property)
  let G0 : Z → ℝ := fun z => if h:z∈s then G ⟨z,h⟩ else 0
  have hG0 : LipschitzOnWith L G0 s := by
    intro x hx y hy
    simpa only [G0,dite_eq_left hx,dite_eq_left hy,Subtype.edist_eq] using hG ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,he⟩ := hG0.extend_real
  have heq (z:s) : G z=g z := by simpa only [G0,dite_eq_left z.property] using he z.property
  refine ⟨g,a,ha,hg,?_,?_⟩
  · intro z hz
    rw [← heq ⟨z,hz⟩]
    exact hGb ⟨z,hz⟩
  · intro ε hε
    have hu := (Metric.tendstoUniformly_iff.mp hlim) ε hε
    filter_upwards [hu] with k hk
    intro z hz
    have hh := hk ⟨z,hz⟩
    simpa only [Real.dist_eq,heq,abs_sub_comm] using hh

end RegularPointCoordinates

end

end OAI
