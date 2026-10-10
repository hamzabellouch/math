import OAI.Probability.FreeIsing.Gaussian.FiniteGaussianPlanted
import OAI.Probability.FreeIsing.Ising.GaussianPosterior
import OAI.Probability.FreeIsing.Posterior.Limit
import OAI.Probability.FreeIsing.Posterior.Symmetry
import OAI.Probability.FreeIsing.Trees.ConnectedExhaustion
import OAI.Probability.FreeIsing.Trees.GibbsField

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace Problem367

open PlantedSymmetry

local instance infinitePosteriorFieldNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

def finiteObservation {d : ℕ} (D : Finset (TreeVertex d)) (t : ℝ≥0)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : D → ℝ :=
  D.restrict (observation t p)

theorem measurable_finiteObservation {d : ℕ} (D : Finset (TreeVertex d)) (t : ℝ≥0) :
    Measurable (finiteObservation D t) :=
  D.measurable_restrict.comp (measurable_observation t)

theorem gaussianPlanted_restrict_joint_law {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (D : Finset (TreeVertex d)) (t : ℝ≥0) :
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map
      (fun p => (D.restrict p.1, finiteObservation D t p)) =
      (μ.map D.restrict) ⊗ₘ finiteGaussianObservationKernel t
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) := by
  let R : ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) →
      (D → IsingSpin) × (D → ℝ) := Prod.map D.restrict D.restrict
  have hR : Measurable R := D.measurable_restrict.prodMap D.measurable_restrict
  have hRlaw : (μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map R =
      (μ.map D.restrict).prod (Measure.pi (fun _ : D => gaussianReal 0 t)) := by
    simpa only [R, gaussianNoiseLaw, Measure.infinitePi_map_restrict] using
      (Measure.map_prod_map μ (gaussianNoiseLaw (TreeVertex d) t)
        D.measurable_restrict D.measurable_restrict).symm
  let F : (D → IsingSpin) × (D → ℝ) → (D → IsingSpin) × (D → ℝ) :=
    fun p => (p.1, fun v => (t : ℝ) * spinSign (p.1 v) + p.2 v)
  have hF : Measurable F := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro v
    exact (measurable_const.mul
      ((measurable_of_finite spinSign).comp ((measurable_pi_apply v).comp measurable_fst))).add
      ((measurable_pi_apply v).comp measurable_snd)
  have : IsProbabilityMeasure (μ.map D.restrict) := inferInstance
  calc
    _ = ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map R).map F := by
      rw [Measure.map_map hF hR]
      rfl
    _ = _ := by
      rw [hRlaw]
      exact finiteGaussianPlanted_joint_law (μ.map D.restrict) t
        (fun (eta : D → IsingSpin) v => spinSign (eta v))

theorem HasFreeIsingLaw.finiteObservation_condExp {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0)
    (q : (D → IsingSpin) → ℝ) :
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
      fun p => q (D.restrict p.1) |
      MeasurableSpace.comap (finiteObservation D t) inferInstance] =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) q (finiteObservation D t p) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (μ.map D.restrict) := inferInstance
  exact FiniteBayes.condExp_state_eq_of_posterior_integral
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (μ.map D.restrict)
    (finiteGaussianObservationKernel t (fun (eta : D → IsingSpin) v => spinSign (eta v)))
    (fun p => D.restrict p.1) (finiteObservation D t)
    (D.measurable_restrict.comp measurable_fst) (measurable_finiteObservation D t)
    (gaussianPlanted_restrict_joint_law μ D t) q _
    (hμ.gaussian_restrict_posterior_mean D hD t q)

theorem finiteIsingPosterior_tanh_bounds {d : ℕ} {beta : ℝ}
    (hbeta : 0 ≤ beta) (D : Finset (TreeVertex d)) (y : D → ℝ) (v : D) :
    Real.tanh (y v - (d : ℝ) * beta) ≤
      FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) w => spinSign (eta w))
        (fun eta => spinSign (eta v)) y ∧
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) w => spinSign (eta w))
        (fun eta => spinSign (eta v)) y ≤ Real.tanh (y v + (d : ℝ) * beta) := by
  have hmem := FinitePosterior.fieldMean_spin_mem_Ioo (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) y
    (fun eta => by cases eta v <;> simp [spinSign])
    ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩
  have hb := finite_tree_gibbs_field_uniform_bound D hbeta y v
  change |Real.artanh (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) y) - y v| ≤ (d : ℝ) * beta at hb
  have hmono : Monotone Real.tanh := by
    apply monotone_of_deriv_nonneg
    · intro x
      exact (hasDerivAt_tanh_response x).differentiableAt
    · intro x
      rw [(hasDerivAt_tanh_response x).deriv]
      exact (sub_pos.mpr (Real.tanh_sq_lt_one x)).le
  have hlo := hmono (show y v - (d : ℝ) * beta ≤
    Real.artanh (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) y) by linarith [(abs_le.mp hb).1])
  have hhi := hmono (show Real.artanh (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) y) ≤ y v + (d : ℝ) * beta by
        linarith [(abs_le.mp hb).2])
  rw [Real.tanh_artanh hmem] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem HasFreeIsingLaw.finiteObservation_spin_tanh_bounds {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (v : D) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Real.tanh (observation t p v.1 - (d : ℝ) * beta) ≤
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
          fun p => spinSign (p.1 v.1) |
          MeasurableSpace.comap (finiteObservation D t) inferInstance] p ∧
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
          fun p => spinSign (p.1 v.1) |
          MeasurableSpace.comap (finiteObservation D t) inferInstance] p ≤
        Real.tanh (observation t p v.1 + (d : ℝ) * beta) := by
  filter_upwards [hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v))]
    with p hp
  change (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun p => spinSign (p.1 v.1) |
    MeasurableSpace.comap (finiteObservation D t) inferInstance] p = _ at hp
  rw [hp]
  exact finiteIsingPosterior_tanh_bounds hbeta D (finiteObservation D t p) v

def finiteObservationFiltration {d : ℕ} (D : ℕ → Finset (TreeVertex d))
    (hD : Monotone D) (t : ℝ≥0) :
    Filtration ℕ (inferInstance : MeasurableSpace
      ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))) where
  seq n := MeasurableSpace.comap (finiteObservation (D n) t) inferInstance
  mono' n m h := by
    change MeasurableSpace.comap (fun p (v : D n) => observation t p v.1) inferInstance ≤
      MeasurableSpace.comap (fun p (v : D m) => observation t p v.1) inferInstance
    rw [MeasurableSpace.comap_process_pi, MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro v
    exact le_iSup_of_le (⟨v.1, hD h v.2⟩ : D m) le_rfl
  le' n := (measurable_finiteObservation (D n) t).comap_le

theorem finiteObservationFiltration_iSup {d : ℕ}
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hex : ∀ v, ∃ n, v ∈ D n) (t : ℝ≥0) :
    (⨆ n, finiteObservationFiltration D hD t n) = observationSigma (TreeVertex d) t := by
  change (⨆ n, MeasurableSpace.comap
    (fun p (v : D n) => observation t p v.1) inferInstance) =
    MeasurableSpace.comap (fun p (v : TreeVertex d) => observation t p v) inferInstance
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def]
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro v
    exact le_iSup_of_le v.1 le_rfl
  · apply iSup_le
    intro v
    obtain ⟨n, hn⟩ := hex v
    exact le_iSup_of_le n (le_iSup_of_le (⟨v, hn⟩ : D n) le_rfl)

theorem HasFreeIsingLaw.posterior_field_bound_of_exhaustion {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hv : ∀ n, v ∈ D n)
    (hex : ∀ w, ∃ n, w ∈ D n) (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p ∈
        Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (posteriorMagnetization
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p) - observation t p v| ≤
        (d : ℝ) * beta := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hb (n : ℕ) := hμ.finiteObservation_spin_tanh_bounds hbeta
    (D n) (hconn n) t ⟨v, hv n⟩
  have hlim := tendsto_posterior_fields_ae
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => observation t p v) ((d : ℝ) * beta) hb
  rw [finiteObservationFiltration_iSup D hD hex t] at hlim
  filter_upwards [hlim] with p hp
  exact ⟨hp.1, hp.2.1⟩

theorem HasFreeIsingLaw.gaussian_posterior_field_bound {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p ∈
        Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (posteriorMagnetization
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p) - observation t p v| ≤
        (d : ℝ) * beta := by
  obtain ⟨D, hD, hconn, hex⟩ := exists_connected_exhaustion v
  exact hμ.posterior_field_bound_of_exhaustion hbeta v D hD
    (fun n => (hconn n).1) (fun n => (hconn n).2) hex t

end Problem367

end

end OAI
