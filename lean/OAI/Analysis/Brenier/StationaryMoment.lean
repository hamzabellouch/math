import OAI.Analysis.Brenier.CellMeasure
import OAI.Analysis.Brenier.Flux
import OAI.Analysis.Brenier.MomentAlgebra

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem358.StationaryMoment

open MidpointEnergy MomentCouplingBounds

variable {ι A F : Type*} [Fintype ι] [MeasurableSpace A]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [InnerProductSpace ℝ F] in
/-- A partition expressed by scaled pushforward laws gives its weighted
quadratic-potential integral identity. -/
theorem integral_partition_pushforwards
    (μ : ι → Measure A) [∀ i, IsFiniteMeasure (μ i)]
    (X : ι → A → F) (w : ι → ℝ) (ρ : Measure F) (R : ℝ)
    (hX : ∀ i, MemLp (X i) 2 (μ i)) (hw : ∀ i, 0 ≤ w i)
    (hpartition : (∑ i, ENNReal.ofReal (w i) • Measure.map (X i) (μ i)) = ρ) :
    (∫ x, quadraticPotential R x ∂ρ) =
      ∑ i, w i * ∫ a, quadraticPotential R (X i a) ∂μ i := by
  have hΦ : StronglyMeasurable (quadraticPotential R (F := F)) :=
    (show Continuous (quadraticPotential R (F := F)) by
      unfold quadraticPotential
      fun_prop).stronglyMeasurable
  have hmap (i : ι) : Integrable (quadraticPotential R)
      (Measure.map (X i) (μ i)) := by
    apply (integrable_map_measure hΦ.aestronglyMeasurable (hX i).aemeasurable).2
    exact (integrable_const _).sub ((hX i).integrable_norm_pow (by norm_num))
  rw [← hpartition, integral_finsetSum_measure
    (fun i _ => (hmap i).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hw i), smul_eq_mul,
    integral_map (hX i).aemeasurable hΦ.aestronglyMeasurable]

/-- The full finite-difference moment estimate assembled from actual midpoint
measure domination and endpoint partition laws. The existence of those dominated
couplings is an explicit input, not a conclusion of this theorem. -/
theorem conditional_stationary_moment_finite_difference
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (X Z : ι → A → F) (η : ι → Measure F) (ρ : Measure F)
    [∀ i, IsFiniteMeasure (η i)]
    (M α β γ : ι → ℝ) {R : ℝ}
    (hX : ∀ i, MemLp (X i) 2 (μ i)) (hZ : ∀ i, MemLp (Z i) 2 (μ i))
    (hR : 0 ≤ R) (hM : ∀ i, 0 < M i)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hαM : ∀ i, α i ≤ 2 * M i) (hγM : ∀ i, M i / 2 ≤ γ i)
    (hγsq : ∀ i, γ i ^ 2 = α i * β i)
    (hXR : ∀ i, ∀ᵐ a ∂μ i, ‖X i a‖ ≤ R)
    (hZR : ∀ i, ∀ᵐ a ∂μ i, ‖Z i a‖ ≤ R)
    (hηR : ∀ i, ∀ᵐ x ∂η i, ‖x‖ ≤ R)
    (hpartition : (∑ i, η i) = ρ)
    (hminus : (∑ i, ENNReal.ofReal (α i) • Measure.map (X i) (μ i)) = ρ)
    (hplus : (∑ i, ENNReal.ofReal (β i) • Measure.map (Z i) (μ i)) = ρ)
    (hdom : ∀ i, ENNReal.ofReal (γ i) •
      Measure.map (fun a => (1 / 2 : ℝ) • (X i a + Z i a)) (μ i) ≤ η i) :
    (∑ i, ‖α i • (∫ a, X i a ∂μ i) - β i • (∫ a, Z i a ∂μ i)‖ ^ 2 / M i) ≤
      162 * R ^ 2 * ∑ i, (α i - β i) ^ 2 / M i := by
  let D : ι → ℝ := fun i => ∫ a, ‖X i a - Z i a‖ ^ 2 ∂μ i
  let Am : ι → ℝ := fun i => ∫ a, quadraticPotential R (X i a) ∂μ i
  let Ap : ι → ℝ := fun i => ∫ a, quadraticPotential R (Z i a) ∂μ i
  have hγ : ∀ i, 0 < γ i := fun i =>
    lt_of_lt_of_le (half_pos (hM i)) (hγM i)
  have hD : ∀ i, 0 ≤ D i := fun i => integral_nonneg (fun _ => sq_nonneg _)
  have hAm : ∀ i, Am i ≤ R ^ 2 := by
    intro i
    have hi : Integrable (fun a => quadraticPotential R (X i a)) (μ i) :=
      (integrable_const _).sub ((hX i).integrable_norm_pow (by norm_num))
    have hh := integral_mono_ae hi (integrable_const (R ^ 2))
      (Filter.Eventually.of_forall (fun a => quadraticPotential_le R (X i a)))
    simpa [Am] using hh
  have hAp : ∀ i, Ap i ≤ R ^ 2 := by
    intro i
    have hi : Integrable (fun a => quadraticPotential R (Z i a)) (μ i) :=
      (integrable_const _).sub ((hZ i).integrable_norm_pow (by norm_num))
    have hh := integral_mono_ae hi (integrable_const (R ^ 2))
      (Filter.Eventually.of_forall (fun a => quadraticPotential_le R (Z i a)))
    simpa [Ap] using hh
  have hdiff : ∀ i, |Am i - Ap i| ≤ 2 * R * Real.sqrt (D i) := by
    intro i
    exact quadratic_potential_expectation_sub_le hR (hX i) (hZ i) (hXR i) (hZR i)
  have haggregate : (∑ i, γ i * ((Am i + Ap i) / 2 + D i / 4)) ≤
      ∑ i, (α i * Am i + β i * Ap i) / 2 := by
    calc
      (∑ i, γ i * ((Am i + Ap i) / 2 + D i / 4)) ≤
          ∑ i, ∫ x, quadraticPotential R x ∂η i := by
        exact Finset.sum_le_sum (fun i _ =>
          scaled_midpoint_energy_le (hγ i).le (hX i) (hZ i) (hηR i) (hdom i))
      _ = ∫ x, quadraticPotential R x ∂ρ := by
        rw [← hpartition]
        symm
        exact integral_finsetSum_measure (fun i _ =>
          integrable_quadraticPotential_of_ae_bound (hηR i))
      _ = ∑ i, (α i * Am i + β i * Ap i) / 2 := by
        have hm := integral_partition_pushforwards μ X α ρ R hX hα hminus
        have hp := integral_partition_pushforwards μ Z β ρ R hZ hβ hplus
        change (∫ x, quadraticPotential R x ∂ρ) =
          ∑ i, (α i * (∫ a, quadraticPotential R (X i a) ∂μ i) +
            β i * (∫ a, quadraticPotential R (Z i a) ∂μ i)) / 2
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← hm, ← hp]
        ring
  have henergy : (∑ i, γ i * D i) ≤
      5 * R ^ 2 * ∑ i, (α i - β i) ^ 2 / γ i :=
    midpoint_aggregate_transport Finset.univ α β γ D Am Ap
      (fun i _ => hα i) (fun i _ => hβ i) (fun i _ => hγ i)
      (fun i _ => hγsq i) (fun i _ => hD i) hR
      (fun i _ => hAm i) (fun i _ => hAp i) (fun i _ => hdiff i) haggregate
  exact stationary_moment_finite_difference M α γ (fun i => α i - β i) D
    (fun i => α i • (∫ a, X i a ∂μ i) - β i • (∫ a, Z i a ∂μ i)) R
    hM hα hαM hγM hD hR
    (fun i => weighted_barycentre_sub_le (hX i) (hZ i) (hα i) (hZR i)) henergy

/-- Geometric data sufficient for one symmetric cell-moment comparison.
In particular, `midpoint_dominated` records the difficult geometric input. -/
structure MidpointComparisonData (Ω : Type*) [MeasurableSpace Ω]
    (M α β : ι → ℝ) (Δ : ι → F) (ρ : Measure F) (R : ℝ) where
  sample : ι → Measure Ω
  sample_probability : ∀ i, IsProbabilityMeasure (sample i)
  leftPoint : ι → Ω → F
  rightPoint : ι → Ω → F
  middleCell : ι → Measure F
  middleCell_finite : ∀ i, IsFiniteMeasure (middleCell i)
  geometricMass : ι → ℝ
  left_memLp : ∀ i, MemLp (leftPoint i) 2 (sample i)
  right_memLp : ∀ i, MemLp (rightPoint i) 2 (sample i)
  left_mass_nonneg : ∀ i, 0 ≤ α i
  right_mass_nonneg : ∀ i, 0 ≤ β i
  left_mass_le : ∀ i, α i ≤ 2 * M i
  geometric_mass_ge : ∀ i, M i / 2 ≤ geometricMass i
  geometric_mass_sq : ∀ i, geometricMass i ^ 2 = α i * β i
  left_bounded : ∀ i, ∀ᵐ a ∂sample i, ‖leftPoint i a‖ ≤ R
  right_bounded : ∀ i, ∀ᵐ a ∂sample i, ‖rightPoint i a‖ ≤ R
  middle_bounded : ∀ i, ∀ᵐ x ∂middleCell i, ‖x‖ ≤ R
  middle_partition : (∑ i, middleCell i) = ρ
  left_partition : (∑ i, ENNReal.ofReal (α i) • Measure.map (leftPoint i) (sample i)) = ρ
  right_partition : (∑ i, ENNReal.ofReal (β i) • Measure.map (rightPoint i) (sample i)) = ρ
  midpoint_dominated : ∀ i, ENNReal.ofReal (geometricMass i) •
    Measure.map (fun a => (1 / 2 : ℝ) • (leftPoint i a + rightPoint i a)) (sample i) ≤
      middleCell i
  moment_difference : ∀ i,
    α i • (∫ a, leftPoint i a ∂sample i) - β i • (∫ a, rightPoint i a ∂sample i) = Δ i

/-- A packaged midpoint comparison proves the uniform finite-difference bound. -/
theorem MidpointComparisonData.finite_difference
    {M α β : ι → ℝ} {Δ : ι → F} {ρ : Measure F} {R : ℝ}
    (data : MidpointComparisonData A M α β Δ ρ R)
    (hR : 0 ≤ R) (hM : ∀ i, 0 < M i) :
    (∑ i, ‖Δ i‖ ^ 2 / M i) ≤ 162 * R ^ 2 * ∑ i, (α i - β i) ^ 2 / M i := by
  let : ∀ i, IsProbabilityMeasure (data.sample i) := data.sample_probability
  let : ∀ i, IsFiniteMeasure (data.middleCell i) := data.middleCell_finite
  have h := conditional_stationary_moment_finite_difference
    data.sample data.leftPoint data.rightPoint data.middleCell ρ M α β data.geometricMass
    data.left_memLp data.right_memLp hR hM data.left_mass_nonneg data.right_mass_nonneg
    data.left_mass_le data.geometric_mass_ge data.geometric_mass_sq
    data.left_bounded data.right_bounded data.middle_bounded data.middle_partition
    data.left_partition data.right_partition data.midpoint_dominated
  simpa only [data.moment_difference] using h

/-- Conditional stationary-site derivative estimate. Its inputs are ordinary
derivatives and actual midpoint comparison data for sufficiently small positive
perturbations; no quantitative limiting inequality is assumed. -/
theorem stationary_moment_derivative_of_midpoint_data
    {B : ι → ℝ → F} {m : ι → ℝ → ℝ} {dB : ι → F} {dm M : ι → ℝ}
    {ρ : Measure F} {R : ℝ}
    (hR : 0 ≤ R) (hM : ∀ i, 0 < M i)
    (hB : ∀ i, HasDerivAt (B i) (dB i) 0)
    (hm : ∀ i, HasDerivAt (m i) (dm i) 0)
    (hdata : ∀ᶠ s : ℝ in 𝓝[>] 0, Nonempty
      (MidpointComparisonData A M (fun i => m i (-s)) (fun i => m i s)
        (fun i => B i (-s) - B i s) ρ R)) :
    (∑ i, ‖dB i‖ ^ 2 / M i) ≤ 162 * R ^ 2 * ∑ i, dm i ^ 2 / M i := by
  apply moment_derivative_bound hB hm
  filter_upwards [hdata] with s hs
  obtain ⟨data⟩ := hs
  exact data.finite_difference hR hM

end Problem358.StationaryMoment

end

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358.StationaryMoment

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- Weighted pair marginals recover the raw unnormalized vector moments. -/
theorem pair_moment_difference
    (π : Measure (F × F)) (ρminus ρplus : Measure F) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hleft : ENNReal.ofReal α • Measure.map Prod.fst π = ρminus)
    (hright : ENNReal.ofReal β • Measure.map Prod.snd π = ρplus) :
    α • (∫ p : F × F, p.1 ∂π) - β • (∫ p : F × F, p.2 ∂π) =
      (∫ x : F, x ∂ρminus) - ∫ x : F, x ∂ρplus := by
  have hf : (∫ x : F, x ∂Measure.map Prod.fst π) = (∫ p : F × F, p.1 ∂π) :=
    integral_map_of_stronglyMeasurable measurable_fst stronglyMeasurable_id
  have hg : (∫ x : F, x ∂Measure.map Prod.snd π) = (∫ p : F × F, p.2 ∂π) :=
    integral_map_of_stronglyMeasurable measurable_snd stronglyMeasurable_id
  rw [← hleft, ← hright, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hα, ENNReal.toReal_ofReal hβ, hf, hg]

/-- Construct the abstract moment witness directly from genuine pair couplings
of the three finite cell partitions. Squared-integrability and the moment
identity are consequences, rather than extra assumptions. -/
def midpointComparisonData_of_pair_couplings
    (π : ι → Measure (F × F)) [∀ i, IsProbabilityMeasure (π i)]
    (ρminus ρplus ρmiddle : ι → Measure F) [∀ i, IsFiniteMeasure (ρmiddle i)]
    (ρ : Measure F) (M α β γ : ι → ℝ) (R : ℝ)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hαM : ∀ i, α i ≤ 2 * M i) (hγM : ∀ i, M i / 2 ≤ γ i)
    (hγsq : ∀ i, γ i ^ 2 = α i * β i)
    (hπ : ∀ i, ∀ᵐ p : F × F ∂π i, ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (hmiddle : ∀ i, ∀ᵐ x : F ∂ρmiddle i, ‖x‖ ≤ R)
    (hleftLaw : ∀ i, ENNReal.ofReal (α i) • Measure.map Prod.fst (π i) = ρminus i)
    (hrightLaw : ∀ i, ENNReal.ofReal (β i) • Measure.map Prod.snd (π i) = ρplus i)
    (hleftPartition : (∑ i, ρminus i) = ρ)
    (hrightPartition : (∑ i, ρplus i) = ρ)
    (hmiddlePartition : (∑ i, ρmiddle i) = ρ)
    (hdom : ∀ i, ENNReal.ofReal (γ i) •
      Measure.map (fun p : F × F => (1 / 2 : ℝ) • (p.1 + p.2)) (π i) ≤ ρmiddle i) :
    MidpointComparisonData (F × F) M α β
      (fun i => (∫ x : F, x ∂ρminus i) - ∫ x : F, x ∂ρplus i) ρ R where
  sample := π
  sample_probability := fun _ => inferInstance
  leftPoint := fun _ => Prod.fst
  rightPoint := fun _ => Prod.snd
  middleCell := ρmiddle
  middleCell_finite := fun _ => inferInstance
  geometricMass := γ
  left_memLp := fun i => MemLp.of_bound continuous_fst.aestronglyMeasurable R
    ((hπ i).mono (fun _ h => h.1))
  right_memLp := fun i => MemLp.of_bound continuous_snd.aestronglyMeasurable R
    ((hπ i).mono (fun _ h => h.2))
  left_mass_nonneg := hα
  right_mass_nonneg := hβ
  left_mass_le := hαM
  geometric_mass_ge := hγM
  geometric_mass_sq := hγsq
  left_bounded := fun i => (hπ i).mono (fun _ h => h.1)
  right_bounded := fun i => (hπ i).mono (fun _ h => h.2)
  middle_bounded := hmiddle
  middle_partition := hmiddlePartition
  left_partition := by simpa only [hleftLaw] using hleftPartition
  right_partition := by simpa only [hrightLaw] using hrightPartition
  midpoint_dominated := hdom
  moment_difference := fun i => pair_moment_difference (π i) (ρminus i) (ρplus i)
    (hα i) (hβ i) (hleftLaw i) (hrightLaw i)

end Problem358.StationaryMoment

end

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem358.StationaryMoment

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- The ordinary measurable, almost-everywhere partition properties of cells. -/
structure AECellPartition (ρ : Measure F) (P : ι → Set F) : Prop where
  measurable : ∀ i, MeasurableSet (P i)
  disjoint : Pairwise (fun i j => AEDisjoint ρ (P i) (P j))
  cover : ∀ᵐ x ∂ρ, x ∈ ⋃ i, P i

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [BorelSpace F]
  [SecondCountableTopology F] in
theorem AECellPartition.sum_restrict {ρ : Measure F} {P : ι → Set F}
    (h : AECellPartition ρ P) : (∑ i, ρ.restrict (P i)) = ρ := by
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion_ae h.disjoint
    (fun i => (h.measurable i).nullMeasurableSet)]
  exact Measure.restrict_eq_self_of_ae_mem h.cover

omit [InnerProductSpace ℝ F] [BorelSpace F] [SecondCountableTopology F] in
/-- Conditioning preserves an almost-everywhere source ball bound. -/
theorem normalizedCellLaw_ae_norm_le {ρ : Measure F} {R : ℝ}
    (hR : ∀ᵐ x ∂ρ, ‖x‖ ≤ R) (P : Set F) :
    ∀ᵐ x ∂normalizedCellLaw ρ P, ‖x‖ ≤ R :=
  Measure.ae_smul_measure (ae_restrict_of_ae hR) _

omit [InnerProductSpace ℝ F] [BorelSpace F] [SecondCountableTopology F] in
/-- A normalized-cell coupling inherits both source ball bounds. -/
theorem normalized_pair_ae_norm_le {ρ : Measure F} {R : ℝ}
    (hR : ∀ᵐ x ∂ρ, ‖x‖ ≤ R) (P Q : Set F) (π : Measure (F × F))
    (hleft : Measure.map Prod.fst π = normalizedCellLaw ρ P)
    (hright : Measure.map Prod.snd π = normalizedCellLaw ρ Q) :
    ∀ᵐ p : F × F ∂π, ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R := by
  have hl : ∀ᵐ x ∂Measure.map Prod.fst π, ‖x‖ ≤ R := by
    rw [hleft]
    exact normalizedCellLaw_ae_norm_le hR P
  have hr : ∀ᵐ x ∂Measure.map Prod.snd π, ‖x‖ ≤ R := by
    rw [hright]
    exact normalizedCellLaw_ae_norm_le hR Q
  exact (ae_of_ae_map measurable_fst.aemeasurable hl).and
    (ae_of_ae_map measurable_snd.aemeasurable hr)

/-- Actual normalized couplings of three cell partitions supply the moment
comparison data. All measure-scaling, partition, boundedness and raw-moment
identities follow from their definitions; midpoint domination remains the
explicit geometric input. -/
def midpointComparisonData_of_normalized_cells
    (ρ : Measure F) [IsFiniteMeasure ρ]
    (Pminus Pplus Pmiddle : ι → Set F)
    (hminus : AECellPartition ρ Pminus) (hplus : AECellPartition ρ Pplus)
    (hmiddle : AECellPartition ρ Pmiddle)
    (hminus_pos : ∀ i, ρ (Pminus i) ≠ 0) (hplus_pos : ∀ i, ρ (Pplus i) ≠ 0)
    (π : ι → Measure (F × F)) [∀ i, IsProbabilityMeasure (π i)]
    (hleft : ∀ i, Measure.map Prod.fst (π i) = normalizedCellLaw ρ (Pminus i))
    (hright : ∀ i, Measure.map Prod.snd (π i) = normalizedCellLaw ρ (Pplus i))
    (M γ : ι → ℝ) (R : ℝ) (hR : ∀ᵐ x ∂ρ, ‖x‖ ≤ R)
    (hαM : ∀ i, ρ.real (Pminus i) ≤ 2 * M i)
    (hγM : ∀ i, M i / 2 ≤ γ i)
    (hγsq : ∀ i, γ i ^ 2 = ρ.real (Pminus i) * ρ.real (Pplus i))
    (hdom : ∀ i, ENNReal.ofReal (γ i) •
      Measure.map (fun p : F × F => (1 / 2 : ℝ) • (p.1 + p.2)) (π i) ≤
        ρ.restrict (Pmiddle i)) :
    MidpointComparisonData (F × F) M (fun i => ρ.real (Pminus i))
      (fun i => ρ.real (Pplus i))
      (fun i => (∫ x in Pminus i, x ∂ρ) - ∫ x in Pplus i, x ∂ρ) ρ R := by
  apply midpointComparisonData_of_pair_couplings π
    (fun i => ρ.restrict (Pminus i)) (fun i => ρ.restrict (Pplus i))
    (fun i => ρ.restrict (Pmiddle i)) ρ M
    (fun i => ρ.real (Pminus i)) (fun i => ρ.real (Pplus i)) γ R
  · exact fun _ => measureReal_nonneg
  · exact fun _ => measureReal_nonneg
  · exact hαM
  · exact hγM
  · exact hγsq
  · exact fun i => normalized_pair_ae_norm_le hR _ _ _ (hleft i) (hright i)
  · exact fun _ => ae_restrict_of_ae hR
  · intro i
    rw [hleft i]
    exact mass_smul_normalizedCellLaw (hminus_pos i) (measure_ne_top _ _)
  · intro i
    rw [hright i]
    exact mass_smul_normalizedCellLaw (hplus_pos i) (measure_ne_top _ _)
  · exact hminus.sum_restrict
  · exact hplus.sum_restrict
  · exact hmiddle.sum_restrict
  · exact hdom

/-- A genuine pair law with normalized cell marginals and the geometric
midpoint domination. No moment inequality is a field of this witness. -/
structure NormalizedMidpointWitness (ρ : Measure F) (P Q H : ι → Set F) where
  coupling : ι → Measure (F × F)
  probability : ∀ i, IsProbabilityMeasure (coupling i)
  left_marginal : ∀ i, Measure.map Prod.fst (coupling i) = normalizedCellLaw ρ (P i)
  right_marginal : ∀ i, Measure.map Prod.snd (coupling i) = normalizedCellLaw ρ (Q i)
  midpoint_dominated : ∀ i, ENNReal.ofReal (Real.sqrt (ρ.real (P i) * ρ.real (Q i))) •
    Measure.map (fun p : F × F => (1 / 2 : ℝ) • (p.1 + p.2)) (coupling i) ≤
      ρ.restrict (H i)

/-- The stationary-site moment derivative bound for actual moving cells.
Only ordinary derivatives and genuine normalized midpoint couplings are
assumed. All nearby mass comparisons follow from continuity. -/
theorem stationary_moment_derivative_of_normalized_cells
    (ρ : Measure F) [IsFiniteMeasure ρ] (P : ℝ → ι → Set F)
    (hP : ∀ s, AECellPartition ρ (P s))
    (R : ℝ) (hR : 0 ≤ R) (hbounded : ∀ᵐ x ∂ρ, ‖x‖ ≤ R)
    (dB : ι → F) (dm : ι → ℝ)
    (hM : ∀ i, 0 < ρ.real (P 0 i))
    (hB : ∀ i, HasDerivAt (fun s => ∫ x in P s i, x ∂ρ) (dB i) 0)
    (hm : ∀ i, HasDerivAt (fun s => ρ.real (P s i)) (dm i) 0)
    (hw : ∀ᶠ s : ℝ in 𝓝[>] 0,
      Nonempty (NormalizedMidpointWitness ρ (P (-s)) (P s) (P 0))) :
    (∑ i, ‖dB i‖ ^ 2 / ρ.real (P 0 i)) ≤
      162 * R ^ 2 * ∑ i, dm i ^ 2 / ρ.real (P 0 i) := by
  have hneg : Filter.Tendsto (fun s : ℝ => -s) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmass := eventually_nearby_mass_bounds (fun i => ρ.real (P 0 i))
    (fun s i => ρ.real (P (-s) i)) (fun s i => ρ.real (P s i)) hM
    (fun i => (hm i).continuousAt.tendsto.comp hneg)
    (fun i => (hm i).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  apply stationary_moment_derivative_of_midpoint_data (A := F × F) hR hM hB hm
  filter_upwards [hw, hmass] with s hs hms
  obtain ⟨w⟩ := hs
  let : ∀ i, IsProbabilityMeasure (w.coupling i) := w.probability
  have hleftpos : ∀ i, ρ (P (-s) i) ≠ 0 := by
    intro i hz
    have hp := (hms i).1
    simp [Measure.real_def, hz] at hp
  have hrightpos : ∀ i, ρ (P s i) ≠ 0 := by
    intro i hz
    have hp := (hms i).2.1
    simp [Measure.real_def, hz] at hp
  exact ⟨midpointComparisonData_of_normalized_cells ρ (P (-s)) (P s) (P 0)
    (hP (-s)) (hP s) (hP 0) hleftpos hrightpos w.coupling
    w.left_marginal w.right_marginal (fun i => ρ.real (P 0 i))
    (fun i => Real.sqrt (ρ.real (P (-s) i) * ρ.real (P s i))) R hbounded
    (fun i => (hms i).2.2.1) (fun i => (hms i).2.2.2)
    (fun i => Real.sq_sqrt (mul_nonneg (hms i).1.le (hms i).2.1.le))
    w.midpoint_dominated⟩

end Problem358.StationaryMoment

end

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Problem358
namespace CellGeometry

/-- The actual distinct-site closed cells form the normalized source partition. -/
theorem aePartition_uniform_closedCell {d : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) :
    StationaryMoment.AECellPartition (uniformMeasure K) (closedCell K y c) where
  measurable i := (isClosed_closedCell hK y c i).measurableSet
  disjoint := pairwise_aedisjoint_closedCell
    (Measure.absolutelyContinuous_restrict.smul_left _) K y c hy
  cover := by
    simpa only [iUnion_closedCell] using UniformSource.ae_mem hK.measurableSet

/-- The raw-volume geometric mean converts to the geometric mean of normalized
cell masses with exactly one source-volume factor. -/
theorem ofReal_sqrt_uniform_cell_masses {d : ℕ} {K U V : Set (E d)}
    (hKpos : 0 < volume K) (hKfinite : volume K ≠ ∞)
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUK : U ⊆ K) (hVK : V ⊆ K) :
    ENNReal.ofReal (Real.sqrt ((uniformMeasure K).real U * (uniformMeasure K).real V)) =
      (volume K)⁻¹ * ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) := by
  rw [uniformMeasure_real_cell hU hUK, uniformMeasure_real_cell hV hVK]
  have hk : 0 < (volume K).toReal := ENNReal.toReal_pos hKpos.ne' hKfinite
  have heq : (volume U).toReal / (volume K).toReal *
      ((volume V).toReal / (volume K).toReal) =
      ((volume U).toReal * (volume V).toReal) / ((volume K).toReal ^ 2) := by ring
  rw [heq, Real.sqrt_div (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
    Real.sqrt_sq hk.le, ENNReal.ofReal_div_of_pos hk, ENNReal.ofReal_toReal hKfinite,
    div_eq_mul_inv, mul_comm]

/-- A raw midpoint coupling supported by a middle cell yields the exact normalized
restricted domination used in the stationary moment estimate. -/
theorem normalized_midpoint_domination {d : ℕ} {K U V H : Set (E d)}
    (hKpos : 0 < volume K) (hKfinite : volume K ≠ ∞)
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hH : MeasurableSet H)
    (hUK : U ⊆ K) (hVK : V ⊆ K) (hHK : H ⊆ K)
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (uniformMeasure U) (uniformMeasure V) π)
    (hsupport : ∀ x ∈ U, ∀ z ∈ V, (1 / 2 : ℝ) • (x + z) ∈ H)
    (hdom : ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
      Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    ENNReal.ofReal (Real.sqrt ((uniformMeasure K).real U * (uniformMeasure K).real V)) •
      Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤
        (uniformMeasure K).restrict H := by
  have hl : ∀ᵐ p : E d × E d ∂π, p.1 ∈ U := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hπ.2.1]
    exact UniformSource.ae_mem hU
  have hr : ∀ᵐ p : E d × E d ∂π, p.2 ∈ V := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact UniformSource.ae_mem hV
  have hm : ∀ᵐ x ∂Measure.map
      (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π, x ∈ H := by
    apply (ae_map_iff (by fun_prop) hH).2
    filter_upwards [hl, hr] with p hp hq
    exact hsupport p.1 hp p.2 hq
  have hraw := Measure.restrict_mono (Subset.refl H) hdom
  rw [Measure.restrict_smul, Measure.restrict_eq_self_of_ae_mem hm] at hraw
  rw [ofReal_sqrt_uniform_cell_masses hKpos hKfinite hU hV hUK hVK,
    mul_smul, uniformMeasure, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset hHK]
  exact smul_le_smul_left _ hraw

/-- A raw dominated coupling of the two opposite intercept cells supplies the
exact normalized cell witness, with all support and normalization requirements
derived from the actual affine cell geometry. -/
theorem normalized_witness_closedCells {d : ℕ} {ι : Type*} [Fintype ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty) (y : ι → E d) (c q : ι → ℝ) (s : ℝ)
    (hraw : ∀ i, ∃ π : Measure (E d × E d),
      IsCoupling (uniformMeasure (closedCell K y (fun j => c j - s * q j) i))
        (uniformMeasure (closedCell K y (fun j => c j + s * q j) i)) π ∧
      ENNReal.ofReal (Real.sqrt
        ((volume (closedCell K y (fun j => c j - s * q j) i)).toReal *
          (volume (closedCell K y (fun j => c j + s * q j) i)).toReal)) •
        Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    Nonempty (StationaryMoment.NormalizedMidpointWitness (uniformMeasure K)
      (closedCell K y (fun j => c j - s * q j))
      (closedCell K y (fun j => c j + s * q j)) (closedCell K y c)) := by
  classical
  choose π hπ hdom using hraw
  have hk : 0 < volume K := Measure.measure_pos_of_nonempty_interior volume hKi
  refine ⟨{ coupling := π
            probability := fun i => (hπ i).1
            left_marginal := ?_
            right_marginal := ?_
            midpoint_dominated := ?_ }⟩
  · intro i
    change Measure.map Prod.fst (π i) =
      NormalizedCell.measure (uniformMeasure K) (closedCell K y (fun j => c j - s * q j) i)
    rw [normalizedCell_uniformMeasure hk hK.measure_ne_top
      (isClosed_closedCell hK.isClosed _ _ _).measurableSet (closedCell_subset _ _ _ _)]
    exact (hπ i).2.1
  · intro i
    change Measure.map Prod.snd (π i) =
      NormalizedCell.measure (uniformMeasure K) (closedCell K y (fun j => c j + s * q j) i)
    rw [normalizedCell_uniformMeasure hk hK.measure_ne_top
      (isClosed_closedCell hK.isClosed _ _ _).measurableSet (closedCell_subset _ _ _ _)]
    exact (hπ i).2.2
  · intro i
    apply normalized_midpoint_domination hk hK.measure_ne_top
      (isClosed_closedCell hK.isClosed _ _ _).measurableSet
      (isClosed_closedCell hK.isClosed _ _ _).measurableSet
      (isClosed_closedCell hK.isClosed _ _ _).measurableSet
      (closedCell_subset _ _ _ _) (closedCell_subset _ _ _ _) (closedCell_subset _ _ _ _)
      (hπ i) ?_ (hdom i)
    intro x hx z hz
    simpa only [smul_add] using midpoint_mem_closedCell hconv y c q i s hx hz

end CellGeometry
end Problem358

namespace Problem358.CellGeometry

/-- Stationary-site moment coercivity for the actual affine cells. The only
geometric input not supplied internally is the convex-body midpoint coupling;
ordinary mass and moment derivatives are left in the form delivered by cell
calculus. In particular no cell partition, scaled-law, nearby-mass, or energy
hypothesis remains. -/
theorem stationary_moment_derivative_of_convex_midpoint
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty) (y : ι → E d) (c q : ι → ℝ)
    (hy : Function.Injective y) (R : ℝ) (hR : 0 ≤ R)
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (dB : ι → E d) (dm : ι → ℝ)
    (hM : ∀ i, 0 < (uniformMeasure K).real (closedCell K y c i))
    (hB : ∀ i, HasDerivAt
      (fun s : ℝ => ∫ x in closedCell K y (fun j => c j + s * q j) i, x ∂uniformMeasure K)
      (dB i) 0)
    (hm : ∀ i, HasDerivAt
      (fun s : ℝ => (uniformMeasure K).real (closedCell K y (fun j => c j + s * q j) i))
      (dm i) 0)
    (hmid : ∀ (U V : Set (E d)), IsCompact U → Convex ℝ U → 0 < volume U →
      IsCompact V → Convex ℝ V → 0 < volume V →
      ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure U) (uniformMeasure V) π ∧
        ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    (∑ i, ‖dB i‖ ^ 2 / (uniformMeasure K).real (closedCell K y c i)) ≤
      162 * R ^ 2 * ∑ i, dm i ^ 2 / (uniformMeasure K).real (closedCell K y c i) := by
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hKi
  let P : ℝ → ι → Set (E d) := fun s => closedCell K y (fun j => c j + s * q j)
  have hzero : P 0 = closedCell K y c := by
    simp only [P, zero_mul, add_zero]
  have hP : ∀ s, StationaryMoment.AECellPartition (uniformMeasure K) (P s) :=
    fun s => aePartition_uniform_closedCell hK.isClosed y _ hy
  have hmass0 : ∀ i, 0 < (uniformMeasure K).real (P 0 i) := by rwa [hzero]
  have hneg : Filter.Tendsto (fun s : ℝ => -s) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmass := eventually_nearby_mass_bounds (fun i => (uniformMeasure K).real (P 0 i))
    (fun s i => (uniformMeasure K).real (P (-s) i))
    (fun s i => (uniformMeasure K).real (P s i)) hmass0
    (fun i => (hm i).continuousAt.tendsto.comp hneg)
    (fun i => (hm i).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hvol {A : Set (E d)} (ha : 0 < (uniformMeasure K).real A) : 0 < volume A := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hzero' : (uniformMeasure K).real A = 0 := by
      simp only [Measure.real_def, hac hz, ENNReal.toReal_zero]
    exact ha.ne' hzero'
  have hw : ∀ᶠ s : ℝ in 𝓝[>] 0,
      Nonempty (StationaryMoment.NormalizedMidpointWitness (uniformMeasure K)
        (P (-s)) (P s) (P 0)) := by
    filter_upwards [hmass] with s hs
    have hraw : ∀ i, ∃ π : Measure (E d × E d),
        IsCoupling (uniformMeasure (closedCell K y (fun j => c j - s * q j) i))
          (uniformMeasure (closedCell K y (fun j => c j + s * q j) i)) π ∧
        ENNReal.ofReal (Real.sqrt
          ((volume (closedCell K y (fun j => c j - s * q j) i)).toReal *
            (volume (closedCell K y (fun j => c j + s * q j) i)).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume := by
      intro i
      apply hmid _ _ (isCompact_closedCell hK _ _ _) (convex_closedCell hconv _ _ _) _
        (isCompact_closedCell hK _ _ _) (convex_closedCell hconv _ _ _) _
      · apply hvol
        simpa only [P, neg_mul, sub_eq_add_neg] using (hs i).1
      · exact hvol (hs i).2.1
    simpa only [P, neg_mul, sub_eq_add_neg, zero_mul, add_zero] using
      normalized_witness_closedCells hK hconv hKi y c q s hraw
  have h := StationaryMoment.stationary_moment_derivative_of_normalized_cells
    (uniformMeasure K) P hP R hR hbounded dB dm hmass0 hB hm hw
  simpa only [hzero] using h

end Problem358.CellGeometry

end

end OAI
