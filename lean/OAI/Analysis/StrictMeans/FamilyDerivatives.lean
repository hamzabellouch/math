import OAI.Analysis.StrictMeans.AffineAveraging

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma continuous_holomorphicFamily_deriv {X : Type*} [TopologicalSpace X] {U : Set ℂ}
    (hU : IsOpen U) (F : X → ℂ → ℂ)
    (hF : Continuous (fun p : X × U => F p.1 p.2))
    (hd : ∀ x, DifferentiableOn ℂ (F x) U) :
    Continuous (fun p : X × U => deriv (F p.1) p.2) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let g : X → C(U, ℂ) := fun x => ⟨fun z => F x z,
    hF.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g hF
  let g' : X → C(U, ℂ) := fun x => ⟨fun z => deriv (F x) z,
    ((hd x).deriv hU).continuousOn.comp_continuous continuous_subtype_val (fun z => z.property)⟩
  have hg' : Continuous g' := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
    have hh : TendstoLocallyUniformlyOn F (F x) (𝓝 x) U := by
      rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
      exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hg.tendsto x)
    have hh' := hh.deriv (Eventually.of_forall hd) hU
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at hh'
    exact hh'
  exact hg'.comp continuous_fst |>.eval continuous_snd

lemma complex_path_norm_hasDerivAt {g : ℝ → ℂ} {b : ℂ} {x : ℝ}
    (hg : HasDerivAt g b x) (hne : g x ≠ 0) :
    HasDerivAt (fun t => ‖g t‖) ((conj (g x) * b).re / ‖g x‖) x := by
  have hn := hg.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hn
  have hi : inner ℝ (g x) b = (conj (g x) * b).re := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
    change (b * conj (g x)).re = _
    rw [mul_comm]
  rw [hi] at hn
  convert hn using 1
  ring

lemma complex_path_normFirst_hasDerivAt {g g' : ℝ → ℂ} {b c : ℂ} {x : ℝ}
    (hg : HasDerivAt g b x) (hg' : HasDerivAt g' c x) (hb : g' x = b)
    (hne : g x ≠ 0) :
    HasDerivAt (fun t => (conj (g t) * g' t).re / ‖g t‖)
      (((conj b * b + conj (g x) * c).re) / ‖g x‖ -
        ((conj (g x) * b).re) ^ 2 / ‖g x‖ ^ 3) x := by
  have hconj : HasDerivAt (fun t => conj (g t)) (conj b) x :=
    Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hg
  have htop := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hconj.mul hg')
  have hnorm := complex_path_norm_hasDerivAt hg hne
  have he := htop.div hnorm (norm_ne_zero_iff.mpr hne)
  have he' : HasDerivAt (fun t => (conj (g t) * g' t).re / ‖g t‖)
      (((conj b * b + conj (g x) * c).re * ‖g x‖ -
        (conj (g x) * b).re * ((conj (g x) * b).re / ‖g x‖)) / ‖g x‖ ^ 2) x := by
    simpa only [Function.comp_apply, Complex.reCLM_apply, Pi.mul_apply, Pi.div_apply, hb] using! he
  convert he' using 1
  field_simp

lemma complex_normSecond_at_one (b c : ℂ) :
    ((conj b * b + conj (1 : ℂ) * c).re) / ‖(1 : ℂ)‖ -
        ((conj (1 : ℂ) * b).re) ^ 2 / ‖(1 : ℂ)‖ ^ 3 = c.re + b.im ^ 2 := by
  simp only [map_one, one_mul, norm_one, div_one, one_pow, add_re, mul_re, conj_re, conj_im]
  ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma compactFamily_hasDerivAt_integral {X E : Type*} [TopologicalSpace X]
    [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ] {F G : ℝ → X → E}
    {s : Set ℝ} {t₀ : ℝ} (hs : IsCompact s) (ht : s ∈ 𝓝 t₀)
    (hF : Continuous (fun p : X × s => F p.2 p.1))
    (hG : Continuous (fun p : X × s => G p.2 p.1))
    (hd : ∀ x t, t ∈ s → HasDerivAt (fun t => F t x) (G t x) t) :
    HasDerivAt (fun t => ∫ x, F t x ∂μ) (∫ x, G t₀ x ∂μ) t₀ := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds ht
  have hcF (t : ℝ) (hts : t ∈ s) : Continuous (F t) :=
    hF.comp (continuous_id.prodMk (continuous_const (y := (⟨t, hts⟩ : s))))
  have hcG (t : ℝ) (hts : t ∈ s) : Continuous (G t) :=
    hG.comp (continuous_id.prodMk (continuous_const (y := (⟨t, hts⟩ : s))))
  obtain ⟨C, hC⟩ := isCompact_range hG |>.isBounded.exists_norm_le
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le ht
    (F := F) (F' := G) (bound := fun _ => C) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · filter_upwards [ht] with t hts using (hcF t hts).aestronglyMeasurable
  · exact (hcF t₀ ht₀).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hcG t₀ ht₀).aestronglyMeasurable
  · exact Eventually.of_forall fun x t hts => hC _ ⟨(x, ⟨t, hts⟩), rfl⟩
  · exact Eventually.of_forall hd

end
end StrictInverseFirstPower

end

end OAI
