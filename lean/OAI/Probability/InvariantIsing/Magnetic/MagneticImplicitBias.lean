import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldInverse
import OAI.Probability.InvariantIsing.Fields.FieldRealVariance

namespace OAI

/-! Parametric inversion of a strictly increasing physical mean spin.
This supplies the finite-dimensional inverse-coordinate and envelope steps
without assuming differentiability of the minimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma parametric_bias_continuousAt {A : ℝ × ℝ → ℝ} {b : ℝ → ℝ} {t s : ℝ}
    (hc : ∀ z, ContinuousAt (fun q => A (q, z)) t)
    (hm : ∀ᶠ q in 𝓝 t, StrictMono (fun z => A (q, z)))
    (he : ∀ᶠ q in 𝓝 t, A (q, b q) = s) : ContinuousAt b t := by
  have het := he.self_of_nhds
  have hmt := hm.self_of_nhds
  apply tendsto_order.2
  constructor
  · intro l hl
    have hlt : A (t, l) < s := by rw [← het]; exact hmt hl
    have hn : ∀ᶠ q in 𝓝 t, A (q, l) < s :=
      (hc l).tendsto.eventually (Iio_mem_nhds hlt)
    filter_upwards [hm, he, hn] with q hmq heq hq
    apply hmq.lt_iff_lt.mp
    rwa [heq]
  · intro u hu
    have htu : s < A (t, u) := by rw [← het]; exact hmt hu
    have hn : ∀ᶠ q in 𝓝 t, s < A (q, u) :=
      (hc u).tendsto.eventually (Ioi_mem_nhds htu)
    filter_upwards [hm, he, hn] with q hmq heq hq
    apply hmq.lt_iff_lt.mp
    rwa [heq]

/-- The implicit bias derivative follows from the derivative of the actual
mean-spin map and the local root equation. -/
lemma parametric_bias_hasDerivAt {A : ℝ × ℝ → ℝ} {b : ℝ → ℝ} {t s a c : ℝ}
    (hb : ContinuousAt b t) (hc : c ≠ 0)
    (hA : HasFDerivAt A (pairLinear a c) (t, b t))
    (he : ∀ᶠ q in 𝓝 t, A (q, b q) = s) :
    HasDerivAt b (-a / c) t := by
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (pairLinear a c)
  let M : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (pairLinear (-a / c) (1 / c))
  have hleft : Function.LeftInverse M L := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · rfl
    · change -a / c * x + (1 / c) * (a * x + c * y) = y
      field_simp [hc]
      ring
  have hf : HasFDerivAt (fun p : ℝ × ℝ => (p.1, A p)) L (t, b t) :=
    hasFDerivAt_fst.prodMk hA
  have hg : ContinuousAt (fun q => (q, b q)) t := continuousAt_id.prodMk hb
  have hh : HasFDerivAt (fun q : ℝ => (q, s))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) t :=
    (hasFDerivAt_id t).prodMk (hasFDerivAt_const s t)
  have hcomp : (fun p : ℝ × ℝ => (p.1, A p)) ∘ (fun q => (q, b q)) =ᶠ[𝓝 t]
      (fun q => (q, s)) := by
    filter_upwards [he] with q hq
    exact congrArg (Prod.mk q) hq
  have hd := HasFDerivAt.of_comp_of_leftInverse hg hf hh hcomp hleft
  have hsnd := hd.snd.hasDerivAt
  convert hsnd using 1
  simp [M, pairLinear]

/-- Envelope differentiation with the bias response derived, rather than
postulated, from the physical mean-spin equation. -/
lemma parametric_bias_envelope {U A : ℝ × ℝ → ℝ} {b : ℝ → ℝ}
    {t s a c v : ℝ} (hb : ContinuousAt b t) (hc : c ≠ 0)
    (hA : HasFDerivAt A (pairLinear a c) (t, b t))
    (he : ∀ᶠ q in 𝓝 t, A (q, b q) = s)
    (hU : HasFDerivAt U (pairLinear v s) (t, b t)) :
    HasDerivAt (fun q => U (q, b q) - b q * s) v t := by
  have hdb := parametric_bias_hasDerivAt hb hc hA he
  have hp := (hasDerivAt_id t).prodMk hdb
  have hd := (hU.comp_hasDerivAt t hp).sub (hdb.mul_const s)
  convert hd using 1
  · rfl
  · simp only [pairLinear_apply]
    ring

end InvariantIsing

end

end OAI
