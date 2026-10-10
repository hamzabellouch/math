import OAI.Probability.FreeIsing.Gaussian.NoiseAverageL2
import OAI.Probability.FreeIsing.Posterior.PlantedStationarity
import OAI.Probability.FreeIsing.Spectral.FreeLawSpectral
import OAI.Probability.FreeIsing.Spectral.LocalOrthogonality

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367.NoisyLocalCovariance
open PlantedStationarity

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

abbrev noiseLaw (ν : Measure A) : Measure (TreeVertex d → A) :=
  Measure.infinitePi (fun _ : TreeVertex d => ν)

def averageBlock (ν : Measure A) (O : IsingSpin → A → B)
    (s : Finset (TreeVertex d)) (F : (s → B) → ℝ) (z : s → IsingSpin) : ℝ :=
  ∫ W : TreeVertex d → A, F (fun i => O (z i) (W i)) ∂noiseLaw ν

theorem measurable_averageBlock (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F) :
    Measurable (averageBlock ν O s F) := by
  have h : Measurable (fun p : (s → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 i) (p.2 i))) := by
    apply hF.comp
    apply Measurable.of_eval
    intro i
    change Measurable ((Function.uncurry O) ∘
      (fun p : (s → IsingSpin) × (TreeVertex d → A) => (p.1 i, p.2 i)))
    exact hO.comp (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply (i : TreeVertex d)).comp measurable_snd))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem averageBlock_reindex (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F)
    (z : s → IsingSpin) (g : TreeAut d) :
    (∫ W, F (fun i => O (z i) (W (g.toEquiv.symm i))) ∂noiseLaw ν) =
      averageBlock ν O s F z := by
  have hm : Measurable (fun W : TreeVertex d → A => F (fun i => O (z i) (W i))) := by
    apply hF.comp
    apply Measurable.of_eval
    intro i
    exact hO.comp (measurable_const.prodMk (measurable_pi_apply (i : TreeVertex d)))
  have h := integral_map (μ := noiseLaw ν) (measurable_relabel g).aemeasurable
    hm.aestronglyMeasurable
  rw [(measurePreserving_iid_relabel ν g).map_eq] at h
  exact h.symm

theorem integral_noise_mul_reindex (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F)
    (g : TreeAut d) (hs : Disjoint s (s.map g.toEquiv.symm.toEmbedding))
    (x : TreeVertex d → IsingSpin) :
    (∫ W, F (fun i => O (x i) (W i)) *
      F (fun i => O (x (g.toEquiv.symm i)) (W (g.toEquiv.symm i))) ∂noiseLaw ν) =
      averageBlock ν O s F (fun i => x i) *
      averageBlock ν O s F (fun i => x (g.toEquiv.symm i)) := by
  have hleft : Measurable (fun W : s → A => F (fun i => O (x i) (W i))) := by
    apply hF.comp
    apply Measurable.of_eval
    intro i
    exact hO.comp (measurable_const.prodMk (measurable_pi_apply i))
  have hright : Measurable (fun W : s → A =>
      F (fun i => O (x (g.toEquiv.symm i)) (W i))) := by
    apply hF.comp
    apply Measurable.of_eval
    intro i
    exact hO.comp (measurable_const.prodMk (measurable_pi_apply i))
  have hind := indepFun_finite_blocks_reindex ν s s g.toEquiv.symm hs
    (fun W => F (fun i => O (x i) (W i)))
    (fun W => F (fun i => O (x (g.toEquiv.symm i)) (W i))) hleft hright
  rw [hind.integral_fun_mul_eq_mul_integral
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  rw [averageBlock_reindex ν hO s hF _ g]
  rfl

theorem averageBlock_memLp (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F)
    (h2 : MemLp (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 i) (p.2 i))) 2 (μ.prod (noiseLaw ν))) :
    MemLp (fun x => averageBlock ν O s F (fun i => x i)) 2 μ ∧
      (∫ x, (averageBlock ν O s F (fun i => x i))^2 ∂μ) ≤
        ∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
          (F (fun i => O (p.1 i) (p.2 i)))^2 ∂μ.prod (noiseLaw ν) := by
  have hm : Measurable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 i) (p.2 i))) := by
    apply hF.comp
    exact (show Measurable (fun x : TreeVertex d → B => fun i : s => x i) from
      Measurable.of_eval (fun i => measurable_pi_apply (i : TreeVertex d))).comp
      (measurable_coordinateMap hO)
  exact memLp_integral_noise hm h2

theorem integral_mul_eq_averaged (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F)
    (g : TreeAut d) (hs : Disjoint s (s.map g.toEquiv.symm.toEmbedding))
    (h2 : MemLp (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 i) (p.2 i))) 2 (μ.prod (noiseLaw ν)))
    (hg2 : MemLp (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 (g.toEquiv.symm i)) (p.2 (g.toEquiv.symm i))))
        2 (μ.prod (noiseLaw ν))) :
    (∫ p, F (fun i => O (p.1 i) (p.2 i)) *
      F (fun i => O (p.1 (g.toEquiv.symm i)) (p.2 (g.toEquiv.symm i)))
        ∂μ.prod (noiseLaw ν)) =
      ∫ x, averageBlock ν O s F (fun i => x i) *
        averageBlock ν O s F (fun i => x (g.toEquiv.symm i)) ∂μ := by
  refine (integral_prod _ (h2.integrable_mul hg2)).trans ?_
  exact integral_congr_ae (Filter.Eventually.of_forall
    (integral_noise_mul_reindex ν hO s hF g hs))

theorem abs_correlation_far {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) {F : (s → B) → ℝ} (hF : Measurable F)
    (h2 : MemLp (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (fun i => O (p.1 i) (p.2 i))) 2 (μ.prod (noiseLaw ν)))
    (hzero : (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F (fun i => O (p.1 i) (p.2 i)) ∂μ.prod (noiseLaw ν)) = 0)
    (g : TreeAut d)
    (hsep : s.sup (fun v => v.val.length) + s.sup (fun v => v.val.length) <
      (g.toEquiv TreeEscape.root).val.length) :
    |∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F (fun i => O (p.1 i) (p.2 i)) *
      F (fun i => O (p.1 (g.toEquiv.symm i)) (p.2 (g.toEquiv.symm i)))
        ∂μ.prod (noiseLaw ν)| ≤
      (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
        (F (fun i => O (p.1 i) (p.2 i)))^2 ∂μ.prod (noiseLaw ν)) *
      theta ^ ((g.toEquiv TreeEscape.root).val.length -
        (s.sup (fun v => v.val.length) + s.sup (fun v => v.val.length))) := by
  classical
  let R := s.sup (fun v => v.val.length)
  let H := averageBlock ν O s F
  let a : (TreeVertex d → IsingSpin) → ℝ := fun x => H (fun i => x i)
  have hH : Measurable H := measurable_averageBlock ν hO s hF
  obtain ⟨ha2, habound⟩ := averageBlock_memLp μ ν hO s hF h2
  have hazero : ∫ x, a x ∂μ = 0 := by
    exact (integral_prod _ (h2.integrable (by norm_num))).symm.trans hzero
  have hagzero : ∫ x, a (relabel g x) ∂μ = 0 :=
    (hμ.integral_relabel g a).trans hazero
  have hag2 := ha2.comp_measurePreserving (hμ.measurePreserving_relabel g)
  have hR : ∀ i : s, i.val.val.length ≤ R := fun i =>
    Finset.le_sup (f := fun v : TreeVertex d => v.val.length) i.property
  have hdepth : (g.symm.toEquiv TreeEscape.root).val.length =
      (g.toEquiv TreeEscape.root).val.length := TreeEscape.symm_root_depth g
  have hb := hμ.abs_correlation_separated_local_blocks h0 h1
    (fun i : s => i.val) (fun i : s => i.val) R hR hR g.symm
    (hdepth ▸ hsep) H H hH hH hazero hagzero ha2 hag2
  have hagsq : (∫ x, (a (relabel g x))^2 ∂μ) = ∫ x, (a x)^2 ∂μ :=
    hμ.integral_relabel g (fun x => (a x)^2)
  change |∫ x, a x * a (relabel g x) ∂μ| ≤
    Real.sqrt (∫ x, (a x)^2 ∂μ) * Real.sqrt (∫ x, (a (relabel g x))^2 ∂μ) *
      theta ^ ((g.symm.toEquiv TreeEscape.root).val.length - (R + R)) at hb
  rw [hagsq, ← pow_two, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (a x))),
    hdepth] at hb
  have hs : Disjoint s (s.map g.toEquiv.symm.toEmbedding) := by
    rw [Finset.map_eq_image]
    exact (TreeEscape.disjoint_inverse_image_of_root_depth g s s hsep).symm
  have hg2 := h2.comp_measurePreserving (measurePreserving_planted_relabel hμ ν g)
  rw [integral_mul_eq_averaged μ ν hO s hF g hs h2 hg2]
  exact hb.trans (mul_le_mul_of_nonneg_right habound (pow_nonneg h0 _))

end Problem367.NoisyLocalCovariance

end

end OAI
