import OAI.Probability.DilutedSpin.AveragedEnergyRoot
import OAI.Probability.DilutedSpin.CavityTrialIdentity
import OAI.Probability.DilutedSpin.MarkMeanProjection

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I Y : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] {A : I → Type} [∀ i,Fintype (A i)] {N J k p L : ℕ}

omit [Countable I] [MeasurableSingletonClass I] in
lemma terminalMean_cavity_marginal [NeZero N]
    (ν : Measure I) (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : (Fin N → Spin) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (θ : Fin k → InteractionSample p) (h : ℝ) (j : Fin k × Fin (p-1) → Fin N) :
    terminalMean ν s Q m ψ Fin.succ
      (fun σ => E (fun i => σ i.succ)+h*spin (σ 0)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) =
    terminalMean ν s Q m ψ id
      (fun σ => E σ+cavitySiteEnergy θ h (fun a => σ (j a))) := by
  unfold terminalMean
  apply integral_congr_ae
  filter_upwards [] with a
  exact terminalRoot_cavity_marginal (fun i : I×Fin N => Q i.1) m hm E
    (rootArray a.1 a.2) (fun i σ b => ψ i.1 (σ i.2) b) θ h j

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] [MeasurableSpace Y] in
lemma energyRoot_eq_locatedTerminalRoot [NeZero N]
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (field : Y → ℝ) (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath (I×Fin N))) (E : (Fin N → Spin) → ℝ) :
    energyRoot (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ) h a E =
      locatedTerminalRoot Q m ψ id (fun σ => E σ+∑ i,field (rootArray N h i)*spin (σ i)) a.2 := rfl

omit [Countable I] [MeasurableSingletonClass I] in
lemma averagedEnergyRoot_eq_terminalMean [NeZero N]
    (ξ : Measure Y) (ν : Measure I) (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (field : Y → ℝ) (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (E : (Fin N → Spin) → ℝ) :
    averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1)
      m field (locatedFactor ψ) E =
      ∫ h,terminalMean ν s Q m ψ id
        (fun σ => E σ+∑ i,field (rootArray N h i)*spin (σ i)) ∂rootLaw N (fun _ => ξ) := rfl

lemma integrable_locatedTerminalRoot [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    Integrable (fun a : Sigma (RootPath (I×Fin J)) => locatedTerminalRoot Q m ψ site E a.2)
      (compoundRootLaw (ν.prod (finiteUniform (Fin J))) s) := by
  exact familyLaw_integrable_bound (poissonMeasure s)
    (fun k => rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))
    (fun k a => locatedTerminalRoot Q m ψ site E a) (fun k => measurable_of_countable _)
    ((integrable_const ‖E‖).add ((poisson_integrable_count s).const_mul D))
    (fun k a => locatedTerminalRoot_bound Q m hm ψ site E hf a)

lemma terminalMean_bound [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |terminalMean ν s Q m ψ site E|≤‖E‖+D*s := by
  rw [terminalMean_count_integral ν s Q m hm ψ site E hf]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ k : ℕ,‖E‖+D*k ∂poissonMeasure s := by
      apply integral_mono
      · exact (poisson_average_integrable s _
          (fun k => abs_integral_le_bound (fun a => locatedTerminalRoot_bound Q m hm ψ site E hf a))).abs
      · exact (integrable_const _).add ((poisson_integrable_count s).const_mul D)
      · intro k
        exact abs_integral_le_bound (fun a => locatedTerminalRoot_bound Q m hm ψ site E hf a)
    _ = _ := by
      rw [integral_add (integrable_const _) ((poisson_integrable_count s).const_mul D),
        integral_const_mul,poisson_mean]
      simp

lemma terminalMean_lipschitz [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    LipschitzWith 1 (terminalMean ν s Q m ψ site) := by
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,terminalMean]
  rw [← integral_sub (integrable_locatedTerminalRoot ν s Q m hm ψ site E hf)
    (integrable_locatedTerminalRoot ν s Q m hm ψ site F hf)]
  apply abs_integral_le_bound
  intro a
  apply root_base_stability _ (fun i : I×Fin J => Q i.1) m hm
  intro y
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (E-F) (terminalState L y)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
