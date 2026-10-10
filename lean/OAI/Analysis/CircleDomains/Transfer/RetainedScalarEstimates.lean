import OAI.Analysis.CircleDomains.Topology.RetainedCircleModel
import OAI.Analysis.CircleDomains.Selection.RealSequenceRetention
import OAI.Analysis.CircleDomains.Transfer.TransportedRealLocalization

namespace OAI

/-! Energy and terminal oscillation estimates for the unchanged scalar tests
on the actual finite stages of the selected circle model. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem intervalFiberHull_value_of_continuousAt
    {X : Type*} [TopologicalSpace X] {U : Set X} {f : X → ℝ} {x : X}
    (hf : ContinuousAt f x) {t : ℝ} (ht : (x, t) ∈ intervalFiberHull (clusterGraph U f)) :
    t = f x := by
  obtain ⟨a, b, s, ha, hb, _, ht⟩ := mem_intervalFiberHull_iff.mp ht
  rw [clusterGraph_fiber_eq_of_continuousAt hf ha,
    clusterGraph_fiber_eq_of_continuousAt hf hb] at ht
  nlinarith [ht]

 theorem FiniteTransfer.CountableRealCoordinates.width_zero_of_continuous
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ) (l : ℕ) (hc : Continuous (d.coordinate l)) (s : S) :
    d.upper l s - d.lower l s = 0 := by
  have hle : d.lower l s ≤ d.upper l s := sub_nonneg.mp (d.width_nonneg l s)
  have hlo : (σ s, d.lower l s) ∈ intervalFiberHull (clusterGraph d.source (d.coordinate l)) := by
    have h : d.lower l s ∈ {t | (σ s, t) ∈ intervalFiberHull (clusterGraph d.source (d.coordinate l))} :=
      (d.band l s).symm ▸ (show d.lower l s ∈ Icc (d.lower l s) (d.upper l s) from ⟨le_rfl, hle⟩)
    exact h
  have hhi : (σ s, d.upper l s) ∈ intervalFiberHull (clusterGraph d.source (d.coordinate l)) := by
    have h : d.upper l s ∈ {t | (σ s, t) ∈ intervalFiberHull (clusterGraph d.source (d.coordinate l))} :=
      (d.band l s).symm ▸ (show d.upper l s ∈ Icc (d.lower l s) (d.upper l s) from ⟨hle, le_rfl⟩)
    exact h
  rw [intervalFiberHull_value_of_continuousAt hc.continuousAt hhi,
    intervalFiberHull_value_of_continuousAt hc.continuousAt hlo, sub_self]

variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 def transferred (i : Fin m) (n : ℕ) : ℂ → ℝ :=
  (sphereRealFunction ((R.model.stages n).functions (prefixIndex (R.index i) n)) ∘
    (R.model.stages n).inverse) ∘ ((↑) : ℂ → Sphere)

 theorem width_zero (i : Fin m) (hQ : Continuous (Q i).quotient) (s : R.marks) :
    R.coordinates.upper (R.index i) s - R.coordinates.lower (R.index i) s = 0 :=
  R.coordinates.width_zero_of_continuous (R.index i) (R.quotient i ▸ hQ) s

 theorem eventually_oscillation (i : Fin m) (hQ : Continuous (Q i).quotient) :
    ∀ᶠ n in atTop, Real.sqrt (∑' s : (R.model.stages n).indices,
      terminalOscillation ((R.model.stages n).terminals.H s)
        ((R.model.stages n).functions (prefixIndex (R.index i) n)) ^ 2) < modelError n := by
  filter_upwards [prefixIndex_eq (R.index i)] with n hn
  have ho := (R.model.stages n).oscillation (prefixIndex (R.index i) n)
  simpa only [hn, R.width_zero i hQ, zero_pow (by decide : 2 ≠ 0),
    tsum_zero, Real.sqrt_zero, zero_add] using ho

 theorem eventually_energy (i : Fin m) :
    ∀ᶠ n in atTop,
      IntegrableOn (euclideanGradientEnergy (R.transferred i n))
        (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) ∧
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain),
        euclideanGradientEnergy (R.transferred i n) z) <
      (∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + modelError n := by
  filter_upwards [prefixIndex_eq (R.index i)] with n hn
  let M := R.model.stages n
  let l := prefixIndex (R.index i) n
  let : Fintype M.indices := M.finite_indices.fintype
  obtain ⟨_, hi, he⟩ := transported_real_energy M.equivalence
    (isOpen_openCompletedRegion M.terminals.H) M.circle_domain.1 M.source_infty M.principal.1
    (M.functions l) (M.functions_smooth_source l) M.metric_conformal
    (fun x _ => M.metric_pos x) (M.functions_integrable_source l)
  have hs := M.source_energy_lt l
  rw [← he] at hs
  refine ⟨hi, ?_⟩
  simpa only [l, hn, R.physical i, M, transferred] using hs

 theorem eventually_retained (i : Fin m) {K : Set Sphere}
    (hK : IsCompact K) (hKG : K ⊆ d.physicalDomain) :
    ∀ᶠ n in atTop, ∀ z : ℂ, (z : Sphere) ∈ K →
      (R.model.stages n).functions (prefixIndex (R.index i) n) (Complex.equivRealProdCLM z) =
        (Q i).physical (Complex.equivRealProdCLM z) := by
  simpa only [R.physical i] using R.model.eventually_test_eq hK hKG (R.index i)

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
