import OAI.Probability.FreeIsing.Brownian.ArrayObservation
import OAI.Probability.FreeIsing.Conditioning.Naturality
import OAI.Probability.FreeIsing.Factors.CoordinateNaturality
import OAI.Probability.FreeIsing.Posterior.PlantedStationarity

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367

lemma measurable_arrayNaturalFiltration_of_intertwining
    {ι Ω : Type*} [MeasurableSpace Ω]
    (X : ι → ℝ≥0 → Ω → ℝ) (hmX : ∀ i t, Measurable (X i t))
    (T : Ω → Ω) (r : ι → ι)
    (hT : ∀ i t ω, X i t (T ω) = X (r i) t ω) (t : ℝ≥0) :
    Measurable[arrayNaturalFiltration X hmX t,
      arrayNaturalFiltration X hmX t] T := by
  rw [arrayNaturalFiltration_eq_comap]
  apply measurable_comap_iff.mpr
  have heq : (fun ω i (s : Set.Iic t) => X i s ω) ∘ T =
      (fun x : ι → Set.Iic t → ℝ => fun i s => x (r i) s) ∘
        (fun ω i (s : Set.Iic t) => X i s ω) := by
    funext ω i s
    exact hT i s ω
  rw [heq]
  exact (Measurable.of_eval fun index =>
    Measurable.of_eval fun time => (measurable_pi_apply time).comp
      (measurable_pi_apply (r index))).comp (comap_measurable _)

theorem ae_all_nnrealTimePrimitive_eq_of_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {m n : ℝ≥0 → Ω → ℝ}
    (hm : Measurable (fun p : ℝ≥0 × Ω => m p.1 p.2))
    (hn : Measurable (fun p : ℝ≥0 × Ω => n p.1 p.2))
    (heq : ∀ t, m t =ᵐ[P] n t) :
    ∀ᵐ ω ∂P, ∀ t, nnrealTimePrimitive m t ω = nnrealTimePrimitive n t ω := by
  have hmR : Measurable (fun p : ℝ × Ω => m p.1.toNNReal p.2) :=
    hm.comp (show Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) by fun_prop)
  have hnR : Measurable (fun p : ℝ × Ω => n p.1.toNNReal p.2) :=
    hn.comp (show Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) by fun_prop)
  have htime : ∀ᵐ ω ∂P, ∀ᵐ (s : ℝ) ∂volume, m s.toNNReal ω = n s.toNNReal ω :=
    (Measure.ae_ae_comm (μ := (volume : Measure ℝ)) (ν := P)
      (p := fun s ω => m s.toNNReal ω = n s.toNNReal ω)
      (measurableSet_eq_fun hmR hnR)).mp
      (Filter.Eventually.of_forall fun (s : ℝ) => heq s.toNNReal)
  filter_upwards [htime] with ω hω
  intro t
  exact intervalIntegral.integral_congr_ae (hω.mono fun _ hs _ => hs)

namespace ArrayPosteriorStationarity

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

def plantedRelabel (g : TreeAut d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) ≃ᵐ
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
  (coordinateRelabelEquiv g.toEquiv).prodCongr (coordinateRelabelEquiv g.toEquiv)

def spinArray (σ : TreeVertex d → IsingSpin) : TreeVertex d → ℝ :=
  fun v => spinSign (σ v)

lemma measurable_spinArray : Measurable (spinArray (d := d)) := by
  have hm : Measurable spinSign := by intro s hs; trivial
  exact Measurable.of_eval fun vertex => hm.comp (measurable_pi_apply vertex)

def filtration (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t)) :
    Filtration ℝ≥0
      (inferInstance : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A))) :=
  arrayObservationFiltration (fun _ : TreeVertex d => B) (fun _ => hmB)
    spinArray measurable_spinArray

lemma measurable_plantedRelabel_filtration
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (g : TreeAut d) (t : ℝ≥0) :
    Measurable[filtration B hmB t, filtration B hmB t] (plantedRelabel (A := A) g) := by
  apply measurable_arrayNaturalFiltration_of_intertwining
    (plantedArrayObservation (fun _ : TreeVertex d => B) spinArray)
    (plantedArrayObservation_measurable (fun _ => hmB) measurable_spinArray)
    (plantedRelabel g) g.toEquiv.symm
  intro i s q
  rfl

lemma measurable_plantedRelabel_symm_filtration
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (g : TreeAut d) (t : ℝ≥0) :
    Measurable[filtration B hmB t, filtration B hmB t] (plantedRelabel (A := A) g).symm := by
  apply measurable_arrayNaturalFiltration_of_intertwining
    (plantedArrayObservation (fun _ : TreeVertex d => B) spinArray)
    (plantedArrayObservation_measurable (fun _ => hmB) measurable_spinArray)
    (plantedRelabel g).symm g.toEquiv
  intro i s q
  rfl

lemma measurePreserving_plantedRelabel {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d) :
    MeasurePreserving (plantedRelabel (A := A) g)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) :=
  PlantedStationarity.measurePreserving_planted_relabel hμ ν g

lemma integrable_spin_coordinate
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    [IsFiniteMeasure P] (v : TreeVertex d) :
    Integrable (fun q => spinSign (q.1 v)) P := by
  have hm : Measurable spinSign := by intro s hs; trivial
  apply Integrable.of_bound
    (hm.comp ((measurable_pi_apply v).comp measurable_fst)).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro q
  cases hs : q.1 v <;> norm_num [spinSign, hs]

def posterior
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ :=
  P[fun q => spinSign (q.1 v) | filtration B hmB t]

lemma measurable_posterior
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : TreeVertex d) : Measurable (posterior P B hmB t v) :=
  stronglyMeasurable_condExp.measurable.mono (filtration B hmB |>.le t) le_rfl

theorem posterior_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (g : TreeAut d) (t : ℝ≥0) (v : TreeVertex d) :
    posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v ∘
        plantedRelabel g =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t
        (g.toEquiv.symm v) := by
  let := hμ.isProbabilityMeasure
  exact condExp_comp_measurePreserving_equiv (filtration B hmB |>.le t)
    (plantedRelabel g) (measurePreserving_plantedRelabel hμ ν g)
    (measurable_plantedRelabel_filtration B hmB g t)
    (measurable_plantedRelabel_symm_filtration B hmB g t)
    (integrable_spin_coordinate _ v)

theorem posterior_version_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {m : ℝ≥0 → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hversion : ∀ t v, m t v =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v)
    (g : TreeAut d) (t : ℝ≥0) (v : TreeVertex d) :
    m t v ∘ plantedRelabel g =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      m t (g.toEquiv.symm v) := by
  exact ((measurePreserving_plantedRelabel hμ ν g).quasiMeasurePreserving.ae_eq_comp
    (hversion t v)).trans ((posterior_relabel_ae hμ ν B hmB g t v).trans
      (hversion t (g.toEquiv.symm v)).symm)

theorem posterior_version_array_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {m : ℝ≥0 → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hversion : ∀ t v, m t v =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v)
    (g : TreeAut d) (t : ℝ≥0) :
    (fun q v => m t v (plantedRelabel g q))
      =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
        (fun q => relabel g (fun v => m t v q)) := by
  filter_upwards [ae_all_iff.mpr
    (fun v => posterior_version_relabel_ae hμ ν B hmB hversion g t v)] with q hq
  exact funext hq

theorem posterior_primitive_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {m : ℝ≥0 → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hm : ∀ v, Measurable (fun p : ℝ≥0 ×
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) => m p.1 v p.2))
    (hversion : ∀ t v, m t v =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v)
    (g : TreeAut d) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)), ∀ v t,
      nnrealTimePrimitive (fun u => m u v) t (plantedRelabel g q) =
        nnrealTimePrimitive (fun u => m u (g.toEquiv.symm v)) t q := by
  let := hμ.isProbabilityMeasure
  apply ae_all_iff.mpr
  intro v
  have hleft : Measurable (fun p : ℝ≥0 ×
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
      m p.1 v (plantedRelabel g p.2)) :=
    (hm v).comp (measurable_fst.prodMk ((plantedRelabel g).measurable.comp measurable_snd))
  exact ae_all_nnrealTimePrimitive_eq_of_version _ hleft (hm (g.toEquiv.symm v))
    (fun t => posterior_version_relabel_ae hμ ν B hmB hversion g t v)

theorem innovation_array_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {m : ℝ≥0 → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hm : ∀ v, Measurable (fun p : ℝ≥0 ×
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) => m p.1 v p.2))
    (hversion : ∀ t v, m t v =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v)
    (g : TreeAut d) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      (fun v t => plantedArrayObservation (fun _ : TreeVertex d => B) spinArray
        v t (plantedRelabel g q) -
          nnrealTimePrimitive (fun u => m u v) t (plantedRelabel g q)) =
      relabel g (fun v t => plantedArrayObservation (fun _ : TreeVertex d => B) spinArray
        v t q - nnrealTimePrimitive (fun u => m u v) t q) := by
  filter_upwards [posterior_primitive_relabel_ae hμ ν B hmB hm hversion g] with q hq
  funext v t
  rw [hq v t]
  rfl

end ArrayPosteriorStationarity
end Problem367

end

end OAI
