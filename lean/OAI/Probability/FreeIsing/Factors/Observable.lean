import OAI.Probability.FreeIsing.Spins.Moments
import OAI.Probability.FreeIsing.Trees.Koopman
import OAI.Probability.FreeIsing.Trees.RootCorrelation

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.FactorObservable

variable {d : ℕ}
variable {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}

def field (Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin))
    (U : TreeVertex d → ℝ) (v : TreeVertex d) : ℝ :=
  (Phi U v).toReal

lemma measurable_field (hPhi : Measurable Phi) (v : TreeVertex d) :
    Measurable (fun U => field Phi U v) :=
  measurable_spinToReal.comp ((measurable_pi_apply v).comp hPhi)

lemma equivariant_field
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U)) :
    ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, field Phi (relabel g U) = relabel g (field Phi U) := by
  intro g
  filter_upwards [heq g] with U hU
  funext v
  exact congrArg IsingSpin.toReal (congrFun hU v)

lemma memLp_field (hPhi : Measurable Phi) (v : TreeVertex d) (p : ENNReal) :
    MemLp (fun U => field Phi U v) p (labelMeasure d) := by
  apply MemLp.of_bound (measurable_field hPhi v).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun U => (norm_spinToReal (Phi U v)).le)

def spinLp (hPhi : Measurable Phi) (v : TreeVertex d) : Lp ℝ 2 (labelMeasure d) :=
  (memLp_field hPhi v 2).toLp (fun U => field Phi U v)

lemma coe_spinLp (hPhi : Measurable Phi) (v : TreeVertex d) :
    (spinLp hPhi v : (TreeVertex d → ℝ) → ℝ) =ᵐ[labelMeasure d]
      (fun U => field Phi U v) :=
  (memLp_field hPhi v 2).coeFn_toLp

lemma norm_spinLp (hPhi : Measurable Phi) (v : TreeVertex d) :
    ‖spinLp hPhi v‖ = 1 := by
  rw [spinLp, Lp.norm_toLp]
  have heq : eLpNorm (fun U => field Phi U v) 2 (labelMeasure d) =
      eLpNorm (fun _ : TreeVertex d → ℝ => (1 : ℝ)) 2 (labelMeasure d) := by
    apply eLpNorm_congr_norm_ae (measurable_field hPhi v).aestronglyMeasurable
      aestronglyMeasurable_const
    exact Filter.Eventually.of_forall (fun U => by
      change ‖(Phi U v).toReal‖ = ‖(1 : ℝ)‖
      rw [norm_spinToReal, norm_one])
  rw [heq, eLpNorm_const' _ (by norm_num) (by norm_num)]
  simp

lemma integral_spinLp {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (v : TreeVertex d) : ∫ U, spinLp hPhi v U ∂labelMeasure d = 0 := by
  exact (integral_congr_ae (coe_spinLp hPhi v)).trans
    (hlaw.integral_factor_spin hPhi v)

lemma spinLp_mem_centered {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (v : TreeVertex d) : spinLp hPhi v ∈ centeredL2 (labelMeasure d) := by
  rw [mem_centeredL2_iff]
  exact integral_spinLp hPhi hlaw v

def centeredSpinLp {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (v : TreeVertex d) : centeredL2 (labelMeasure d) :=
  ⟨spinLp hPhi v, spinLp_mem_centered hPhi hlaw v⟩

@[simp] lemma centeredSpinLp_coe {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d))) (v : TreeVertex d) :
    (centeredSpinLp hPhi hlaw v : Lp ℝ 2 (labelMeasure d)) = spinLp hPhi v := rfl

@[simp] lemma norm_centeredSpinLp {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d))) (v : TreeVertex d) :
    ‖centeredSpinLp hPhi hlaw v‖ = 1 := norm_spinLp hPhi v

lemma koopman_spinLp (hPhi : Measurable Phi)
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U))
    (g : TreeAut d) (v : TreeVertex d) :
    koopmanL2 (relabel g) (measurePreserving_relabel g) (spinLp hPhi v) =
      spinLp hPhi (g.toEquiv.symm v) := by
  change Lp.compMeasurePreserving (relabel g) (measurePreserving_relabel g)
    ((memLp_field hPhi v 2).toLp _) = _
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  filter_upwards [heq g] with U hU
  exact congrArg IsingSpin.toReal (congrFun hU v)

lemma inner_spinLp (hPhi : Measurable Phi) (u v : TreeVertex d) :
    inner ℝ (spinLp hPhi u) (spinLp hPhi v) =
      ∫ U, field Phi U u * field Phi U v ∂labelMeasure d := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_spinLp hPhi u, coe_spinLp hPhi v] with U hu hv
  rw [hu, hv]
  simp [mul_comm]

lemma inner_spinLp_root {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    inner ℝ (spinLp hPhi (ConnectedHull.root d)) (spinLp hPhi v) =
      theta ^ v.1.length := by
  rw [inner_spinLp]
  simpa only [field, IsingSpin.toReal_eq_spinSign] using
    hlaw.factor_root_correlation hPhi hlo hhi v

lemma inner_centeredSpinLp_root {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    inner ℝ (centeredSpinLp hPhi hlaw (ConnectedHull.root d))
      (centeredSpinLp hPhi hlaw v) = theta ^ v.1.length :=
  inner_spinLp_root hPhi hlaw hlo hhi v

lemma inner_koopman_spinLp_root {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U))
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (g : TreeAut d) :
    inner ℝ (spinLp hPhi (ConnectedHull.root d))
      (koopmanL2 (relabel g) (measurePreserving_relabel g)
        (spinLp hPhi (ConnectedHull.root d))) =
      theta ^ (g.toEquiv.symm (ConnectedHull.root d)).1.length := by
  rw [koopman_spinLp hPhi heq]
  exact inner_spinLp_root hPhi hlaw hlo hhi _

lemma centeredAverage_centeredSpinLp {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U))
    (v : TreeVertex d) :
    TreeKoopman.centeredAverage d (centeredSpinLp hPhi hlaw v) =
      (d : ℝ)⁻¹ • ∑ c : Fin d, centeredSpinLp hPhi hlaw (prefixFlip c v) := by
  apply Subtype.ext
  simp only [TreeKoopman.centeredAverage_apply_coe, Submodule.coe_smul,
    Submodule.coe_sum, centeredSpinLp_coe]
  exact TreeKoopman.average_toLp_eq (field Phi) (equivariant_field heq)
    (fun v => memLp_field hPhi v 2) v

end Problem367.FactorObservable

namespace Problem367

theorem IsFactorOfIID.exists_centered_observable {d : ℕ} {theta : ℝ}
    (hfactor : IsFactorOfIID d theta) (hlo : -1 ≤ theta) (hhi : theta ≤ 1) :
    ∃ f : centeredL2 (labelMeasure d), ‖f‖ = 1 ∧
      ∀ g : TreeAut d,
        inner ℝ (f : Lp ℝ 2 (labelMeasure d))
          (koopmanL2 (relabel g) (measurePreserving_relabel g)
            (f : Lp ℝ 2 (labelMeasure d))) =
          theta ^ (g.toEquiv.symm (ConnectedHull.root d)).1.length := by
  obtain ⟨Phi, hPhi, hlaw, heq⟩ := hfactor
  refine ⟨FactorObservable.centeredSpinLp hPhi hlaw (ConnectedHull.root d),
    FactorObservable.norm_centeredSpinLp hPhi hlaw _, ?_⟩
  intro g
  exact FactorObservable.inner_koopman_spinLp_root hPhi hlaw heq hlo hhi g

end Problem367

end

end OAI
