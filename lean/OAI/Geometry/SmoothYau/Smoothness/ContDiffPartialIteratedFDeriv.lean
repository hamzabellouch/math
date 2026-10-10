import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
namespace YauCounterexamples
section SmoothFamily
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma contDiff_partial_iteratedFDeriv (f : A → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : A × E => iteratedFDeriv ℝ n (f p.1) p.2) := by
  induction n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.uncurry_def, ContinuousLinearEquiv.coe_coe] using!
      ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.contDiff.comp hf)
  | succ n ih =>
    have hh : ContDiff ℝ ∞ (fun z : (A × E) × E => iteratedFDeriv ℝ n (f z.1.1) z.2) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hd : ContDiff ℝ ∞ (fun z : A × E => fderiv ℝ (iteratedFDeriv ℝ n (f z.1)) z.2) :=
      hh.fderiv contDiff_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ContinuousLinearEquiv.coe_coe] using!
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm.toContinuousLinearEquiv.contDiff.comp hd)

end SmoothFamily
section CompactFamily
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem tendsto_schwartz_of_common_support
    (f : ℝ → 𝓢(E, F)) (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
    (K : Set E) (hK : IsCompact K) (hsupp : ∀ r, tsupport (f r) ⊆ K)
    (hzero : f 0 = 0) : Tendsto f (𝓝 0) (𝓝 0) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  have hc : Continuous (fun p : ℝ × K => ‖(p.2 : E)‖ ^ k *
      ‖iteratedFDeriv ℝ n (f p.1) (p.2 : E)‖) := by
    exact ((continuous_subtype_val.comp continuous_snd).norm.pow k).mul
      (((contDiff_partial_iteratedFDeriv (fun r x => f r x) hf n).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).norm)
  have hu := Continuous.tendstoUniformly
    (fun r (x : K) => ‖(x : E)‖ ^ k * ‖iteratedFDeriv ℝ n (f r) (x : E)‖) hc 0
  have he : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ x : K,
      ‖(x : E)‖ ^ k * ‖iteratedFDeriv ℝ n (f r) (x : E)‖ < ε / 2 := by
    have hu' := (Metric.tendstoUniformly_iff.mp hu) (ε / 2) (by positivity)
    filter_upwards [hu'] with r hr
    intro x
    simpa [hzero, dist_comm, Real.dist_eq, abs_of_nonneg (by positivity :
      0 ≤ ‖(x : E)‖ ^ k * ‖iteratedFDeriv ℝ n (f r) (x : E)‖)] using hr x
  filter_upwards [he] with r hr
  simp only [sub_zero, SchwartzMap.schwartzSeminormFamily_apply]
  apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n (f r) (by positivity) ?_)
    (half_lt_self hε)
  intro x
  by_cases hx : x ∈ K
  · exact (hr ⟨x, hx⟩).le
  · have hz : iteratedFDeriv ℝ n (f r) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hx (hsupp r (tsupport_iteratedFDeriv_subset n h))
    simp only [hz, norm_zero, mul_zero]
    positivity

end CompactFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rescaledCoefficient (f χ : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) (r : ℝ) : 𝓢(E, ℂ) :=
  (hχc.mul_right (f' := fun x => f (p + r • x) - f p)).toSchwartzMap
    (hχ.mul ((hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id))).sub contDiff_const))

lemma rescaledCoefficient_tendsto (f χ : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) :
    Tendsto (rescaledCoefficient f χ hf hχ hχc p) (𝓝 0) (𝓝 0) := by
  apply tendsto_schwartz_of_common_support _ ?_ (tsupport χ) hχc ?_ ?_
  · change ContDiff ℝ ∞ (fun z : ℝ × E => χ z.2 * (f (p + z.1 • z.2) - f p))
    exact (hχ.comp contDiff_snd).mul
      ((hf.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))).sub contDiff_const)
  · intro r
    exact tsupport_mul_subset_left
  · ext x
    simp [rescaledCoefficient]

end YauCounterexamples

end

end OAI
