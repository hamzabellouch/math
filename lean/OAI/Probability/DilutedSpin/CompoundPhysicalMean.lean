import OAI.Probability.DilutedSpin.CompoundRate
import OAI.Probability.DilutedSpin.RandomInsertion

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped NNReal ENNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

noncomputable def energyRoot (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath I)) (E : (Fin N → Spin) → ℝ) : ℝ :=
  root (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m
    (fun y => E (terminalState L y)+∑ i,field (rootArray N h i)*spin (terminalState L y i))
    (rootArray a.1 a.2) factor

omit [MeasurableSpace Y] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma energyRoot_lipschitz (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath I)) :
    LipschitzWith 1 (energyRoot Q m field factor h a) := by
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  apply root_base_stability _ Q m hm
  intro y
  simp only [add_sub_add_right_eq_sub]
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (E-F) (terminalState L y)

noncomputable def rootSample (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (n : ℕ) (a : RootPath I n) : ℝ :=
  root (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m
    (fun y => energy V field h k x (terminalState L y)) (rootArray n a) factor

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma measurable_rootSample_fixed
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hV : Measurable V) (hh : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (k n : ℕ) (a : RootPath I n) :
    Measurable (fun z : RootPath Y N × RootPath X k =>
      rootSample V field Q m factor z.1 k z.2 n a) := by
  let b := fun z : RootPath Y N × RootPath X k =>
    fun y : FinitePath (Fin N → Spin) (L+1) => energy V field z.1 k z.2 (terminalState L y)
  have hb : ∀ y,Measurable (fun z => b z y) := fun y =>
    measurable_energy V field (fun σ => (measurable_pi_apply σ).comp hV) hh k _
  exact measurable_root (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m b
    (rootArray n a) (fun _ => factor) hb (fun _ _ _ => measurable_const)

lemma measurable_rootSample
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hV : Measurable V) (hh : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (k n : ℕ) :
    Measurable (fun z : (RootPath Y N × RootPath X k) × RootPath I n =>
      rootSample V field Q m factor z.1.1 k z.1.2 n z.2) := by
  apply measurable_from_prod_countable_left
  intro a
  exact measurable_rootSample_fixed V field hV hh Q m factor k n a

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I] [Countable I]
  [MeasurableSingletonClass I] in
lemma rootSample_bound (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hVb : ∀ x σ,|V x σ|≤C) (hhb : ∀ y,|field y|≤H)
    (hfb : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (n : ℕ) (a : RootPath I n) :
    |rootSample V field Q m factor h k x n a|≤H*N+C*k+D*n := by
  exact root_uniform_bound _ Q m hm _ _ factor
    (fun y => energy_bound V field hVb hhb h k x _) hfb

omit [MeasurableSpace Y] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma integral_compound_energyRoot (μ : Measure X) [IsProbabilityMeasure μ] (r : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ) (hV : Measurable V)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath I)) :
    (∫ z : Sigma (RootPath X),rootSample V field Q m factor h z.1 z.2 a.1 a.2 ∂compoundRootLaw μ r)=
      ∫ E,energyRoot Q m field factor h a E ∂compoundPoisson r (Measure.map V μ) := by
  have he : Measurable (fun z : Sigma (RootPath X) => ∑ i,V (rootArray z.1 z.2 i)) := by
    apply measurable_sigmaUncurry (f := fun n (x : RootPath X n) => ∑ i,V (rootArray n x i))
    intro k
    simpa only [rootArrayEquiv_apply] using
      (show Measurable (fun x : RootPath X k => ∑ i,V (rootArrayEquiv (X := X) k x i)) by fun_prop)
  rw [← map_compoundRoot_energy μ V hV r,
    integral_map he.aemeasurable (energyRoot_lipschitz Q m hm field factor h a).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [rootSample,energyRoot,energy,Finset.sum_apply]

lemma fullRoot_energy_integral
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hV : Measurable V) (hh : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hVb : ∀ x σ,|V x σ|≤C) (hhb : ∀ y,|field y|≤H)
    (hfb : ∀ i y a,|Real.log (factor i y a)|≤D) :
    (∫ z,packRoot (rootSample V field Q m factor) z ∂fullRootLaw (fun _ => ξ) μ ν r s) =
      ∫ h,∫ a,∫ E,energyRoot Q m field factor h a E
        ∂compoundPoisson r (Measure.map V μ) ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ) := by
  rw [integral_fullRootLaw_reordered (fun _ => ξ) μ ν r s
    (measurable_rootSample V field hV hh Q m factor)
    (fun h k x n a => (rootSample_bound V field Q m hm factor hVb hhb hfb h k x n a).trans
      (count_linear_le_quadratic hC hD k n))]
  apply integral_congr_ae
  filter_upwards [] with h
  apply integral_congr_ae
  filter_upwards [] with a
  exact integral_compound_energyRoot μ r V field hV Q m hm factor h a

end DilutedSpinGlass.PhysicalRoot

end

end OAI
