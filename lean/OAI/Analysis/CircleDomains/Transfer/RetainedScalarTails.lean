import OAI.Analysis.CircleDomains.Transfer.RetainedScalarEstimates

namespace OAI

/-! The actual retained planar exhaustion has vanishing original energy
outside it. The same finite models transfer this tail estimate to the target. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace FiniteTransfer.RealModelExhaustion
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

def realPlane (n : ℕ) : Set (ℝ × ℝ) := Complex.equivRealProdCLM.symm ⁻¹' M.plane n

theorem realPlane_open (n : ℕ) : IsOpen (M.realPlane n) :=
  (M.plane_open n).preimage Complex.equivRealProdCLM.symm.continuous

theorem realPlane_monotone : Monotone M.realPlane := fun _ _ h => preimage_mono (M.plane_monotone h)

theorem realPlane_core (n : ℕ) : M.realPlane n ⊆ (M.stages n).core := by
  intro x hx
  apply interior_subset ((M.stages n).core_contains ?_)
  exact M.plane_core n (Or.inl ⟨Complex.equivRealProdCLM.symm x, hx, rfl⟩)

theorem iUnion_realPlane : (⋃ n, M.realPlane n) = realChartDomain G := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact (M.stages n).core_source (M.realPlane_core n hn)
  · intro hx
    have hp : ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈
        ((↑) : ℂ → Sphere) '' (⋃ n, M.plane n) ∪ {OnePoint.infty} := M.exhausts.symm ▸ hx
    rcases hp with ⟨z, hz, he⟩ | hp
    · have he' : z = Complex.equivRealProdCLM.symm x := OnePoint.coe_injective he
      subst z
      obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨n, hn⟩
    · exact (OnePoint.coe_ne_infty (Complex.equivRealProdCLM.symm x) hp).elim

theorem source_energy_tail_tendsto (l : ℕ) :
    Tendsto (fun n => ∫ x in realChartDomain G \ M.realPlane n,
      gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x)
      atTop (𝓝 0) := by
  have hi : IntegrableOn
      (gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1))
      (realChartDomain G) :=
    integrable_gradientEnergy_spherical_of_memLp (d.physical_energy l)
  have hmeas : MeasurableSet (realChartDomain G) := by
    rw [← M.iUnion_realPlane]
    exact MeasurableSet.iUnion fun n => (M.realPlane_open n).measurableSet
  have h := tendsto_setIntegral_of_antitone
    (fun n => hmeas.diff (M.realPlane_open n).measurableSet)
    (fun i j hij => sdiff_subset_sdiff Subset.rfl (M.realPlane_monotone hij))
    (show ∃ n, IntegrableOn
      (gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1))
      (realChartDomain G \ M.realPlane n) from ⟨0, hi.mono_set sdiff_subset⟩)
  have he : (⋂ n, realChartDomain G \ M.realPlane n) = ∅ := by
    ext x
    simp only [mem_iInter, Set.mem_sdiff, mem_empty_iff_false, iff_false]
    intro hx
    have hxin : x ∈ ⋃ n, M.realPlane n := M.iUnion_realPlane.symm ▸ (hx 0).1
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxin
    exact (hx n).2 hn
  simpa only [he, setIntegral_empty] using h

end FiniteTransfer.RealModelExhaustion

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

def targetTail (n : ℕ) : Set ℂ :=
  (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) \
    (Complex.equivRealProdCLM ⁻¹' (sphereRealMap (R.model.stages n).forward '' R.model.realPlane n))

theorem eventually_tail_energy_bound (i : Fin m) :
    ∀ᶠ n in atTop,
      IntegrableOn (euclideanGradientEnergy (R.transferred i n)) (R.targetTail n) ∧
      (∫ z in R.targetTail n, euclideanGradientEnergy (R.transferred i n) z) <
      (∫ x in realChartDomain d.physicalDomain \ R.model.realPlane n,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + modelError n := by
  filter_upwards [prefixIndex_eq (R.index i)] with n hn
  let M := R.model.stages n
  let l := prefixIndex (R.index i) n
  let : Fintype M.indices := M.finite_indices.fintype
  have hsub : R.targetTail n ⊆ Complex.equivRealProdCLM ⁻¹'
      (sphereRealMap M.forward '' (realChartDomain (openCompletedRegion M.terminals.H) \
        R.model.realPlane n)) := by
    intro z hz
    have hzV : Complex.equivRealProdCLM z ∈ realChartDomain M.domain := by
      simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz.1
    obtain ⟨x, hx, hxe⟩ := (M.equivalence.real_bijOn M.source_infty M.principal.1).surjOn hzV
    refine ⟨x, ⟨hx, ?_⟩, hxe⟩
    intro hxE
    exact hz.2 ⟨x, hxE, hxe⟩
  have h := M.transported_energy_away_lt l (R.model.realPlane_open n).measurableSet
    (R.model.realPlane_core n) hsub
  simpa only [l, hn, R.physical i, M, transferred] using h

theorem tail_energy_tendsto (i : Fin m) :
    Tendsto (fun n => ∫ z in R.targetTail n, euclideanGradientEnergy (R.transferred i n) z)
      atTop (𝓝 0) := by
  have hlim := (R.model.source_energy_tail_tendsto (R.index i)).add modelError_tendsto
  simp only [R.physical i, add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun n =>
    integral_nonneg (fun _ => euclideanGradientEnergy_nonneg _ _))
    ((R.eventually_tail_energy_bound i).mono fun _ h => h.2.le) hlim

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
