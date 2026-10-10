import OAI.Probability.FreeIsing.Posterior.ArrayPosteriorStationarity

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ArrayPosteriorStationarity

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

lemma integrable_spin_pair
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    [IsFiniteMeasure P] (v w : TreeVertex d) :
    Integrable (fun q => spinSign (q.1 v) * spinSign (q.1 w)) P := by
  have hm : Measurable spinSign := by intro s hs; trivial
  apply Integrable.of_bound
    (((hm.comp ((measurable_pi_apply v).comp measurable_fst)).mul
      (hm.comp ((measurable_pi_apply w).comp measurable_fst))).aestronglyMeasurable) 1
  apply Filter.Eventually.of_forall
  intro q
  cases hv : q.1 v <;> cases hw : q.1 w <;> norm_num [spinSign, hv, hw]

def posteriorPair
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v w : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ :=
  P[fun q => spinSign (q.1 v) * spinSign (q.1 w) | filtration B hmB t]

def posteriorCovariance
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v w : TreeVertex d)
    (q : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) : ℝ :=
  posteriorPair P B hmB t v w q - posterior P B hmB t v q * posterior P B hmB t w q

lemma measurable_posteriorPair
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v w : TreeVertex d) : Measurable (posteriorPair P B hmB t v w) :=
  stronglyMeasurable_condExp.measurable.mono (filtration B hmB |>.le t) le_rfl

lemma measurable_posteriorCovariance
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v w : TreeVertex d) : Measurable (posteriorCovariance P B hmB t v w) :=
  (measurable_posteriorPair P B hmB t v w).sub
    ((measurable_posterior P B hmB t v).mul (measurable_posterior P B hmB t w))

theorem posteriorPair_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    posteriorPair (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v w ∘
        plantedRelabel g =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posteriorPair (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t
        (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  let := hμ.isProbabilityMeasure
  exact condExp_comp_measurePreserving_equiv (filtration B hmB |>.le t)
    (plantedRelabel g) (measurePreserving_plantedRelabel hμ ν g)
    (measurable_plantedRelabel_filtration B hmB g t)
    (measurable_plantedRelabel_symm_filtration B hmB g t)
    (integrable_spin_pair _ v w)

theorem posteriorCovariance_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    posteriorCovariance (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v w ∘
        plantedRelabel g =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posteriorCovariance (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t
        (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  filter_upwards [posteriorPair_relabel_ae hμ ν B hmB g t v w,
    posterior_relabel_ae hμ ν B hmB g t v,
    posterior_relabel_ae hμ ν B hmB g t w] with q hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp (congrArg₂ (· * ·) hv hw)

theorem posteriorCovariance_version_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {C : ℝ≥0 → TreeVertex d → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hversion : ∀ t v w, C t v w =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posteriorCovariance (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v w)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    C t v w ∘ plantedRelabel g =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      C t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  exact ((measurePreserving_plantedRelabel hμ ν g).quasiMeasurePreserving.ae_eq_comp
    (hversion t v w)).trans ((posteriorCovariance_relabel_ae hμ ν B hmB g t v w).trans
      (hversion t (g.toEquiv.symm v) (g.toEquiv.symm w)).symm)

theorem posteriorCovariance_version_matrix_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {C : ℝ≥0 → TreeVertex d → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hversion : ∀ t v w, C t v w =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posteriorCovariance (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v w)
    (g : TreeAut d) (t : ℝ≥0) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)), ∀ v w,
      C t v w (plantedRelabel g q) = C t (g.toEquiv.symm v) (g.toEquiv.symm w) q := by
  exact ae_all_iff.mpr fun v => ae_all_iff.mpr fun w =>
    posteriorCovariance_version_relabel_ae hμ ν B hmB hversion g t v w

end Problem367.ArrayPosteriorStationarity

end

end OAI
