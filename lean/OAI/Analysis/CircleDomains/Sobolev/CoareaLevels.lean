import OAI.Analysis.CircleDomains.Sobolev.CoareaInput
import OAI.Analysis.CircleDomains.Topology.LevelQuotient
import OAI.Analysis.CircleDomains.Modulus.BandIncidence
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-!
# From planar coarea charts to compact quotient-level topology

A finite collection of Lipschitz parameterizations covers the physical
part of each level. Scalar coarea in each parameter domain gives finite
Hausdorff length almost everywhere. The quotient-level
argument then gives the finite-continuum bound, countably many
nondegenerate components, and local connectedness of every subcontinuum.

The chart-cover inclusion and the compactness of the level are
geometric hypotheses; `PlanarScalarCoarea` supplies the analytic identity.
-/

open Set MeasureTheory Metric Function
open scoped ENNReal NNReal

namespace CircleDomainRigidity

/-- A finite list may repeat labels: its entries still have independent
level parameters. -/
def finiteLevelUnion {X J Λ : Type*} (H : Λ → ℝ → Set X) (labels : J → Λ)
    (θ : J → ℝ) : Set X :=
  ⋃ j, H (labels j) (θ j)

/-- Almost-everywhere finite length for each label passes to an actual
finite union under the independent product of the level measures. -/
theorem ae_finite_hausdorffMeasure_level_union
    {Y J Λ : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Fintype J]
    (μ : Measure ℝ) [SigmaFinite μ] (A : Λ → ℝ → Set Y) (labels : J → Λ)
    (hfinite : ∀ l, ∀ᵐ t ∂μ, (μH[1] : Measure Y) (A l t) < ∞) :
    ∀ᵐ θ ∂Measure.pi (fun _ : J => μ),
      (μH[1] : Measure Y) (finiteLevelUnion A labels θ) < ∞ := by
  have hcoordinate (j : J) : ∀ᵐ θ ∂Measure.pi (fun _ : J => μ),
      (μH[1] : Measure Y) (A (labels j) (θ j)) < ∞ :=
    (Measure.quasiMeasurePreserving_eval (fun _ : J => μ) j).ae (hfinite (labels j))
  filter_upwards [ae_all_iff.mpr hcoordinate] with θ hθ
  apply lt_of_le_of_lt (measure_iUnion_le _)
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.mpr (fun j _ => hθ j)

/-- Finite Lipschitz chart covers preserve the almost-everywhere finite
length conclusion of planar coarea. -/
theorem ae_finite_physical_levels_of_planar_coarea
    {Y ι : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Fintype ι]
    (hcoarea : PlanarScalarCoarea)
    (D : ι → Set ℂ) (f : ι → ℂ → ℝ) (χ : ι → ℂ → Y) (K : ι → ℝ≥0)
    (hD : ∀ i, IsOpen (D i)) (hf : ∀ i, ContDiffOn ℝ 1 (f i) (D i))
    (hχ : ∀ i, LipschitzWith (K i) (χ i))
    (harea : ∀ i, volume (D i) < ∞)
    (henergy : ∀ i, (∫⁻ z in D i, ENNReal.ofReal (‖fderiv ℝ (f i) z‖ ^ 2)) < ∞)
    (A : ℝ → Set Y)
    (hcover : ∀ t, A t ⊆ ⋃ i, χ i ''
      (D i ∩ {z | (f i z : UnitAddCircle) = (t : UnitAddCircle)})) :
    ∀ᵐ (t : ℝ) ∂volume.restrict (Ico (0 : ℝ) 1), (μH[1] : Measure Y) (A t) < ∞ := by
  have hlength (i : ι) := ae_finite_planar_mod_one_levels
    (hcoarea (D i) (hD i) (f i) (hf i)) (harea i) (henergy i)
  filter_upwards [ae_all_iff.mpr hlength] with t ht
  apply lt_of_le_of_lt (measure_mono (hcover t))
  apply lt_of_le_of_lt (measure_iUnion_le _)
  rw [tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  apply lt_of_le_of_lt ((hχ i).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) _)
  simpa only [ENNReal.rpow_one] using ENNReal.mul_lt_top ENNReal.coe_lt_top (ht i)

/-- The actual compact quotient-level conclusions obtained from
Federer's scalar coarea input and a finite planar chart cover. -/
theorem ae_level_topology_of_planar_coarea
    {X Y ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [Fintype ι]
    (hcoarea : PlanarScalarCoarea)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (D : ι → Set ℂ) (f : ι → ℂ → ℝ) (χ : ι → ℂ → Y) (K : ι → ℝ≥0)
    (hD : ∀ i, IsOpen (D i)) (hf : ∀ i, ContDiffOn ℝ 1 (f i) (D i))
    (hχ : ∀ i, LipschitzWith (K i) (χ i))
    (harea : ∀ i, volume (D i) < ∞)
    (henergy : ∀ i, (∫⁻ z in D i, ENNReal.ofReal (‖fderiv ℝ (f i) z‖ ^ 2)) < ∞)
    (H : ℝ → Set X) (hH : ∀ t, IsCompact (H t))
    (hcover : ∀ t, (π ⁻¹' H t) ∩ G ⊆ ⋃ i, χ i ''
      (D i ∩ {z | (f i z : UnitAddCircle) = (t : UnitAddCircle)})) :
    ∀ᵐ (t : ℝ) ∂volume.restrict (Ico (0 : ℝ) 1),
      HasFiniteLargeContinuumBound (H t) ∧
        {C : Set (H t) | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}.Countable ∧
        ∀ C : Set (H t), IsCompact C → IsConnected C → LocallyConnectedSpace C := by
  filter_upwards [ae_finite_physical_levels_of_planar_coarea hcoarea D f χ K
    hD hf hχ harea henergy (fun t => (π ⁻¹' H t) ∩ G) hcover] with t ht
  exact level_topology_of_finite_physical_length π hπ hsurj hfiber
    hG hB hTD hdust (hH t) ht

/-- Generic finite level unions, including repeated labels, satisfy the
physical-length and continuum-topology conclusions. The probability
law is the independent product of Lebesgue measure on `[0,1)`.

This is the coarea-to-topology part of the manuscript's Generic level
continua lemma, items (i)--(iii). Arcwise connectedness is not asserted
by this theorem. All chart geometry remains explicit. -/
theorem ae_finite_level_union_topology_of_planar_coarea
    {X Y J Λ ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    [Fintype J] [Fintype ι]
    (hcoarea : PlanarScalarCoarea)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (D : Λ → ι → Set ℂ) (f : Λ → ι → ℂ → ℝ)
    (χ : Λ → ι → ℂ → Y) (K : Λ → ι → ℝ≥0)
    (hD : ∀ l i, IsOpen (D l i))
    (hf : ∀ l i, ContDiffOn ℝ 1 (f l i) (D l i))
    (hχ : ∀ l i, LipschitzWith (K l i) (χ l i))
    (harea : ∀ l i, volume (D l i) < ∞)
    (henergy : ∀ l i,
      (∫⁻ z in D l i, ENNReal.ofReal (‖fderiv ℝ (f l i) z‖ ^ 2)) < ∞)
    (H : Λ → ℝ → Set X) (hH : ∀ l t, IsCompact (H l t))
    (hcover : ∀ l t, (π ⁻¹' H l t) ∩ G ⊆ ⋃ i, χ l i ''
      (D l i ∩ {z | (f l i z : UnitAddCircle) = (t : UnitAddCircle)}))
    (labels : J → Λ) :
    ∀ᵐ θ ∂Measure.pi (fun _ : J => volume.restrict (Ico (0 : ℝ) 1)),
      (μH[1] : Measure Y) ((π ⁻¹' finiteLevelUnion H labels θ) ∩ G) < ∞ ∧
      HasFiniteLargeContinuumBound (finiteLevelUnion H labels θ) ∧
      {C : Set (finiteLevelUnion H labels θ) |
        (∃ x, C = connectedComponent x) ∧ C.Nontrivial}.Countable ∧
      ∀ C : Set (finiteLevelUnion H labels θ),
        IsCompact C → IsConnected C → LocallyConnectedSpace C := by
  have hlength (l : Λ) := ae_finite_physical_levels_of_planar_coarea hcoarea
    (D l) (f l) (χ l) (K l) (hD l) (hf l) (hχ l) (harea l) (henergy l)
    (fun t => (π ⁻¹' H l t) ∩ G) (hcover l)
  filter_upwards [ae_finite_hausdorffMeasure_level_union
    (volume.restrict (Ico (0 : ℝ) 1))
    (fun l t => (π ⁻¹' H l t) ∩ G) labels hlength] with θ hθ
  have hphysical : (μH[1] : Measure Y)
      ((π ⁻¹' finiteLevelUnion H labels θ) ∩ G) < ∞ := by
    simpa only [finiteLevelUnion, preimage_iUnion, iUnion_inter] using hθ
  have hcompact : IsCompact (finiteLevelUnion H labels θ) :=
    isCompact_iUnion (fun j => hH (labels j) (θ j))
  exact ⟨hphysical, level_topology_of_finite_physical_length π hπ hsurj hfiber
    hG hB hTD hdust hcompact hphysical⟩

/-- The weighted-level numerical estimate: coarea supplies the physical
term, and Tonelli plus the band-incidence bound supplies the countable
dust term. Their sum is finite under the two spatial `L²` assumptions
and the two square-summable dust sequences.

The events `E` and their measure bound are geometric hypotheses, and
weighted scalar coarea supplies the analytic identity. -/
theorem weighted_level_bound_of_planar_coarea
    {S : Type*} [Countable S]
    (hcoarea : WeightedPlanarScalarCoarea) {D : Set ℂ} (hD : IsOpen D)
    {f q : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (hq : Measurable q) (hq0 : ∀ z, 0 ≤ q z)
    (hq2 : (∫⁻ z in D, ENNReal.ofReal (q z ^ 2)) < ∞)
    (hf2 : (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) < ∞)
    (E : S → Set ℝ) (m a : S → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, (volume.restrict (Ico (0 : ℝ) 1)) (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    (∫⁻ t in Ico (0 : ℝ) 1,
      (weightedCircleLevelLength D f (fun z => ENNReal.ofReal (q z)) t +
        weightedBandIncidence E m t)) ≤
      (∫⁻ z in D, ENNReal.ofReal (q z) * ENNReal.ofReal ‖fderiv ℝ f z‖) +
        ENNReal.ofReal (∑' s, m s * a s) ∧
    (∫⁻ t in Ico (0 : ℝ) 1,
      (weightedCircleLevelLength D f (fun z => ENNReal.ofReal (q z)) t +
        weightedBandIncidence E m t)) < ∞ := by
  obtain ⟨hmeas, heq, hfinite, _⟩ :=
    weighted_circle_coarea_of_finite_energy hcoarea hD hf hq hq0 hq2 hf2
  have hbound := lintegral_weightedBandIncidence_le
    (volume.restrict (Ico (0 : ℝ) 1)) E m a hE hm ha hband hm2 ha2
  have htotal : (∫⁻ t in Ico (0 : ℝ) 1,
      (weightedCircleLevelLength D f (fun z => ENNReal.ofReal (q z)) t +
        weightedBandIncidence E m t)) ≤
      (∫⁻ z in D, ENNReal.ofReal (q z) * ENNReal.ofReal ‖fderiv ℝ f z‖) +
        ENNReal.ofReal (∑' s, m s * a s) := by
    rw [lintegral_add_left' hmeas, heq]
    exact add_le_add le_rfl hbound
  refine ⟨htotal, htotal.trans_lt (ENNReal.add_lt_top.mpr ⟨?_, ENNReal.ofReal_lt_top⟩)⟩
  rwa [← heq]

end CircleDomainRigidity

end OAI
