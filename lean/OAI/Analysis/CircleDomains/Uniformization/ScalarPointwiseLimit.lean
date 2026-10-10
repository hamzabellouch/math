import OAI.Analysis.CircleDomains.Uniformization.ActualInverseConvergence
import OAI.Analysis.CircleDomains.Uniformization.ScalarLimitWitness

namespace OAI

/-! The actual bounded scalar fillings converge at every point of the
limiting image to the retained source scalar. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

theorem filled_tendsto_on_image (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (i : Fin m) (F : ∀ n, R.HoleFilling i n) {x : ℂ} (hx : (x : Sphere) ∈ d.physicalDomain) :
    Tendsto (fun n => (F (R.limit.subsequence n)).filled (R.limit.function x))
      atTop (𝓝 ((Q i).physical (Complex.equivRealProdCLM x))) := by
  obtain ⟨r, hr, hrG⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hG.preimage OnePoint.continuous_coe).mem_nhds hx)
  let H := roundJordanAt x r hr
  have hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain := by
    simpa only [H, roundJordanAt_closure] using hrG
  have hxH : x ∈ jordanInterior H := by
    change x ∈ jordanInterior (roundJordanAt x r hr)
    rw [roundJordanAt_interior]
    exact mem_ball_self hr
  have hKG : ((↑) : ℂ → Sphere) '' closure (jordanInterior H) ⊆ d.physicalDomain := by
    rintro _ ⟨z, hz, rfl⟩
    exact hHG hz
  have hK := (isCompact_closure_jordanInterior H).image OnePoint.continuous_coe
  have hevent : ∀ᶠ n in atTop,
      (F (R.limit.subsequence n)).filled (R.limit.function x) =
        clipScalar ((Q i).physical (Complex.equivRealProdCLM
          (finiteCoord ((R.model.stages (R.limit.subsequence n)).inverse (R.limit.function x))))) := by
    filter_upwards [R.limit.eventually_compact_subset_anchor_image hsch hG H hHG
      isCompact_singleton (singleton_subset_iff.mpr (mem_image_of_mem _ hxH)),
      R.limit.strict.tendsto_atTop (R.model.eventually_model_contains hK hKG),
      R.limit.strict.tendsto_atTop (R.eventually_retained i hK hKG)] with n hn hM ht
    obtain ⟨y, hy, he⟩ := hn (mem_singleton (R.limit.function x))
    have hyK := mem_image_of_mem ((↑) : ℂ → Sphere) (subset_closure hy)
    have hyM := hM hyK
    have hyfinite := (R.model.stages (R.limit.subsequence n)).equivalence.finite_forward
      (R.model.stages (R.limit.subsequence n)).source_infty
      (R.model.stages (R.limit.subsequence n)).principal.1 hyM
    have he' : (R.model.stages (R.limit.subsequence n)).forward y =
        (R.limit.function x : Sphere) := by
      change finiteCoord ((R.model.stages (R.limit.subsequence n)).forward y) = R.limit.function x at he
      rw [← coe_finiteCoord hyfinite, he]
    have hi : (R.model.stages (R.limit.subsequence n)).inverse (R.limit.function x) = (y : Sphere) := by
      rw [← he', (R.model.stages (R.limit.subsequence n)).equivalence.left_inv _ hyM]
    rw [(F (R.limit.subsequence n)).filled_on_domain
      (he' ▸ (R.model.stages (R.limit.subsequence n)).equivalence.mapsTo hyM)]
    unfold transferred
    simp only [comp_apply, hi, finiteCoord_coe]
    congr 1
    change (R.model.stages (R.limit.subsequence n)).functions (prefixIndex (R.index i)
      (R.limit.subsequence n)) (Complex.equivRealProdCLM y) = _
    exact ht y hyK
  have hc : ContinuousAt (fun z : ℂ => (Q i).physical (Complex.equivRealProdCLM z)) x := by
    apply ((Q i).physical_smooth.continuousOn.continuousAt
      ((isOpen_realChartDomain hG).mem_nhds ?_)).comp
      Complex.equivRealProdCLM.continuous.continuousAt
    simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hx
  have hlim := (clipScalar_lipschitz.continuous.continuousAt.comp hc).tendsto.comp
    (R.limit.inverse_tendsto hsch hG hx)
  have hu : (Q i).physical (Complex.equivRealProdCLM x) ∈ Icc 0 1 := by
    rw [(Q i).pullback x hx]
    exact (Q i).quotient_unit _
  simp only [comp_def] at hlim
  rw [clipScalar_eq hu] at hlim
  apply hlim.congr'
  filter_upwards [hevent] with n hn
  exact hn.symm

theorem ScalarWeakLimit.pointwise_on_image {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    {x : ℂ} (hx : (x : Sphere) ∈ d.physicalDomain) :
    Tendsto (fun n => (W.fillings (W.subsequence n)).filled (R.limit.function x))
      atTop (𝓝 ((Q i).physical (Complex.equivRealProdCLM x))) := by
  obtain ⟨τ, hτ, he⟩ := W.factor
  rw [he]
  simpa only [comp_def] using
    (R.filled_tendsto_on_image hsch hG i W.fillings hx).comp hτ.tendsto_atTop

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
