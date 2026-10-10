import OAI.Probability.FreeIsing.Energy.NoisyLocalCovariance

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.NoisyLawSpectral
open PlantedStationarity NoisyLocalCovariance

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

abbrev law (μ : Measure (TreeVertex d → IsingSpin)) (ν : Measure A)
    (O : IsingSpin → A → B) : Measure (TreeVertex d → B) :=
  (μ.prod (noiseLaw ν)).map (coordinateMap O)

theorem local_koopman_far_decay {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 (law μ ν O))
    (F : (s → B) → ℝ) (hF : Measurable F)
    (hf : f =ᵐ[law μ ν O] fun x => F (fun i => x i))
    (hzero : ∫ x, f x ∂law μ ν O = 0) :
    ∃ N : ℕ, ∀ g : TreeAut d, N < (g.toEquiv TreeEscape.root).val.length →
      |inner ℝ f (koopmanL2 (relabel g)
        (measurePreserving_coordinateMap_relabel hμ ν O hO g) f)| ≤
        ‖f‖^2 * theta^((g.toEquiv TreeEscape.root).val.length - N) := by
  let f0 : (TreeVertex d → B) → ℝ := fun x => F (fun i => x i)
  have hm0 : Measurable f0 := hF.comp
    (Measurable.of_eval (fun i => measurable_pi_apply (i : TreeVertex d)))
  have hf0 : MemLp f0 2 (law μ ν O) := (memLp_congr_ae hf).mp (Lp.memLp f)
  have hmO := measurable_coordinateMap (d := d) hO
  have hmp : MeasurePreserving (coordinateMap (d := d) O)
      (μ.prod (noiseLaw ν)) (law μ ν O) := ⟨hmO, rfl⟩
  have h2 := hf0.comp_measurePreserving hmp
  have hz0 : (∫ x, f0 x ∂law μ ν O) = 0 := (integral_congr_ae hf).symm.trans hzero
  have hz : (∫ p, f0 (coordinateMap O p) ∂μ.prod (noiseLaw ν)) = 0 :=
    (integral_map hmO.aemeasurable hm0.aestronglyMeasurable).symm.trans hz0
  have hn0 : (∫ x, (f0 x)^2 ∂law μ ν O) = ‖f‖^2 := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    simp [hx, f0, pow_two]
  have hn : (∫ p, (f0 (coordinateMap O p))^2 ∂μ.prod (noiseLaw ν)) = ‖f‖^2 :=
    (integral_map hmO.aemeasurable (hm0.pow_const 2).aestronglyMeasurable).symm.trans hn0
  let R := s.sup (fun v => v.val.length)
  refine ⟨R + R, fun g hg => ?_⟩
  have hb := NoisyLocalCovariance.abs_correlation_far hμ h0 h1 ν hO s hF h2 hz g hg
  change |∫ p, f0 (coordinateMap O p) *
      f0 (relabel g (coordinateMap O p)) ∂μ.prod (noiseLaw ν)| ≤
      (∫ p, (f0 (coordinateMap O p))^2 ∂μ.prod (noiseLaw ν)) *
        theta ^ ((g.toEquiv TreeEscape.root).val.length - (R + R)) at hb
  rw [hn] at hb
  rw [TreeLawKoopman.inner_koopman_eq_integral_of_local (law μ ν O)
    (measurePreserving_coordinateMap_relabel hμ ν O hO) s f F hf g]
  change |∫ x, f0 x * f0 (relabel g x) ∂law μ ν O| ≤ _
  have heq : (∫ x, f0 x * f0 (relabel g x) ∂law μ ν O) =
      ∫ p, f0 (coordinateMap O p) * f0 (relabel g (coordinateMap O p))
        ∂μ.prod (noiseLaw ν) :=
    integral_map hmO.aemeasurable
      (hm0.mul (hm0.comp (measurable_relabel g))).aestronglyMeasurable
  rw [heq]
  exact hb

theorem localCriticalDecay {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O)) :
    TreeLawKoopman.LocalCriticalDecay (law μ ν O)
      (measurePreserving_coordinateMap_relabel hμ ν O hO) := by
  apply TreeLawKoopman.localCriticalDecay_of_far_decay (law μ ν O)
    (measurePreserving_coordinateMap_relabel hμ ν O hO) hd h0 hthreshold
  intro s f F hF hf hzero
  exact local_koopman_far_decay hμ h0 h1 ν hO s f F hF hf hzero

theorem centeredAverage_norm_le_critical {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O)) :
    ‖TreeLawKoopman.centeredAverage (law μ ν O)
      (measurePreserving_coordinateMap_relabel hμ ν O hO)‖ ≤
      2 * Real.sqrt ((d : ℝ) - 1) / d := by
  exact TreeLawKoopman.centeredAverage_norm_le (law μ ν O)
    (measurePreserving_coordinateMap_relabel hμ ν O hO) hd
    (localCriticalDecay hμ hd h0 h1 hthreshold ν hO)

end Problem367.NoisyLawSpectral

end

end OAI
