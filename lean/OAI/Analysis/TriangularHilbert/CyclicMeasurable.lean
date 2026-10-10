import OAI.Analysis.TriangularHilbert.CompactMoment

namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma measurable_cyclicKernelOutput (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (K : ℝ → ℝ) (hK : Measurable K) : Measurable (cyclicKernelOutput B C K) := by
  have hm : Measurable (fun q : (ℝ×ℝ)×ℝ => B (q.1.2,q.2)*C (q.2,q.1.1)*(K (q.1.1+q.1.2+q.2):ℂ)) := by
    apply Measurable.mul
    · exact (hB.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
        (hC.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
    · exact Complex.measurable_ofReal.comp (hK.comp
        (((measurable_fst.comp measurable_fst).add (measurable_snd.comp measurable_fst)).add measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma cyclicKernelOutput_support (B C : ℝ×ℝ → ℂ) {M : ℝ}
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) (hz : z ∉ closedBox M) :
    cyclicKernelOutput B C K z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with c
  by_cases hb : B (z.2,c) = 0
  · simp only [hb,zero_mul,Pi.zero_apply]
  · have hc : C (c,z.1) = 0 := by
      by_contra hc
      exact hz ((mem_closedBox _ _).mpr ⟨(hC _ hc).2,(hB _ hb).1⟩)
    simp only [hc,mul_zero,zero_mul,Pi.zero_apply]

lemma cyclicKernelOutput_bound (B C : ℝ×ℝ → ℂ) {M CB CC L : ℝ}
    (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (_hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    (K : ℝ → ℝ) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ) :
    ‖cyclicKernelOutput B C K z‖ ≤ outputBound M CB CC L := by
  apply norm_integral_le_of_norm_le
    ((integrableOn_const (μ := volume) (s := Set.Icc (-(M+1)) (M+1)) (C := CB*CC*L)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc)
  filter_upwards [] with c
  by_cases hmem : c ∈ Set.Icc (-(M+1)) (M+1)
  · rw [Set.indicator_of_mem hmem,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul (hb _) (hc _) (norm_nonneg _) hCB) (hk _) (abs_nonneg _)
      (mul_nonneg hCB hCC)
  · have he : B (z.2,c) = 0 := by
      by_contra he
      apply hmem
      exact abs_le.mp ((hs _ he).2.trans (by linarith))
    simp only [he,zero_mul,norm_zero,Set.indicator_of_notMem hmem,le_refl]

lemma integrable_cyclic_moment_box (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    {M CB CC L : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (K : κ → ℝ → ℝ)
    (hK : ∀ k, Measurable (K k)) (hk : ∀ k t, |K k t| ≤ L) :
    Integrable (fun z : ℝ×ℝ => finiteMoment (fun k => cyclicKernelOutput B C (K k) z)) := by
  let T := outputBound M CB CC L
  have hT : 0 ≤ T := outputBound_nonneg M hCB hCC hL
  apply ((integrableOn_const (μ := volume) (s := closedBox M) (C := T*Real.sqrt T)
    (volume_closedBox_ne_top _)).integrable_indicator (measurableSet_closedBox _)).mono'
  · exact (continuous_finiteMoment.measurable.comp (Measurable.of_eval
      (fun k => measurable_cyclicKernelOutput B C hB hC (K k) (hK k)))).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_of_nonneg (finiteMoment_nonneg _)]
    by_cases hz : z ∈ closedBox M
    · rw [Set.indicator_of_mem hz]
      exact finiteMoment_le _ (fun k => cyclicKernelOutput_bound B C hsB hCB hCC hL hb hc (K k) (hk k) z)
    · have he : (fun k => cyclicKernelOutput B C (K k) z) = fun _ : κ => (0:ℂ) :=
        funext (fun k => cyclicKernelOutput_support B C hsB hsC (K k) z hz)
      rw [he,finiteMoment_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg hT (Real.sqrt_nonneg _)) z
end
end TriangularHilbert.Heat
end

end OAI
