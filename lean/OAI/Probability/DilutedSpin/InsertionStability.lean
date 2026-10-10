import OAI.Probability.DilutedSpin.CompoundPoisson
import OAI.Probability.DilutedSpin.PhysicalInsertionLimit

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma map_familyLaw_sum {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    {Y : Type*} [MeasurableSpace Y] (μ : Measure I) (ν : ∀ i, Measure (X i))
    (f : (i : I) → X i → Y) (hf : ∀ i, Measurable (f i)) :
    Measure.map (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) =
      Measure.sum (fun i => μ {i} • Measure.map (f i) (ν i)) := by
  rw [familyLaw,Measure.comp_eq_sum_of_countable]
  rw [Measure.map_sum (measurable_sigmaUncurry hf).aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul _ (measurable_sigmaUncurry hf).aemeasurable]
  change μ {i} • Measure.map (fun z : Sigma X => f z.1 z.2)
    (Measure.map (Sigma.mk i) (ν i)) = _
  rw [Measure.map_map (measurable_sigmaUncurry hf) (measurable_sigmaMk i)]
  rfl

variable {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] in
lemma map_iid_energy (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (n : ℕ) :
    Measure.map (fun x : RootPath X n => ∑ i, V (rootArray n x i)) (rootLaw n (fun _ => μ)) =
      Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => Measure.map V μ)) := by
  have hp := (measurePreserving_rootArray μ n).map_eq
  rw [← Measure.pi_map_pi (fun _ : Fin n => hV.aemeasurable)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← hp,Measure.map_map (by fun_prop) (rootArrayEquiv n).measurable]
  congr 1
  funext x
  simp only [Function.comp_apply,rootArrayEquiv_apply]

omit [NormedSpace ℝ E] in
/-- The physical recursive Poisson container has exactly the compound-sum
energy law, including its independent random count. -/
lemma map_compoundRoot_energy (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (r : ℝ≥0) :
    Measure.map (fun z : Sigma (RootPath X) => ∑ i, V (rootArray z.1 z.2 i)) (compoundRootLaw μ r) =
      compoundPoisson r (Measure.map V μ) := by
  rw [compoundRootLaw,map_familyLaw_sum _ _ (fun n x => ∑ i,V (rootArray n x i)) (fun n => by
    simpa only [rootArrayEquiv_apply] using
      (show Measurable (fun x : RootPath X n => ∑ i,V (rootArrayEquiv (X := X) n x i)) by fun_prop))]
  simp only [poissonMeasure_singleton,map_iid_energy μ V hV,compoundPoisson]

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {ι : Type} [Fintype ι]
lemma spinLog_stability (F G : (ι → Spin) → ℝ) {D : ℝ}
    (h : ∀ s, |F s-G s|≤D) (x : ι → ℝ) : |spinLog F x-spinLog G x|≤D := by
  classical
  apply weighted_log_exp_stability _ _ _ (fun s => (Finset.prod_pos (fun i _ => q_pos _ _)).le) _ h
  rw [← Fintype.prod_sum]
  simp only [q_sum,Finset.prod_const_one]
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped BigOperators
variable {p : ℕ}
lemma reservoirInsertion_lipschitz (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) : LipschitzWith 1 (reservoirInsertion M C H N L u a) := by
  apply LipschitzWith.of_dist_le_mul
  intro F G
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  have hi (F : (Fin a → Spin) → ℝ) : Integrable
      (sameInsertionAverage (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
        (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M C H N)
        (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
        (physicalSpin N L) a F) (reservoirLaw M N L) := by
    apply MeasureMean.bounded_integrable
    · exact measurable_sameInsertionAverage _ _ _ _ _ _ (measurable_physicalBase M C H N) a F
    · intro z
      exact sameInsertionAverage_bound _ _ _ _ _ _ (gridExponents_pos L) a F
        (fun s => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm F s) z
  unfold reservoirInsertion
  rw [← integral_sub (hi F) (hi G)]
  apply abs_integral_le_bound
  intro z
  unfold sameInsertionAverage
  rw [← FiniteLaw.expect_sub]
  apply FiniteLaw.abs_expect_le
  intro i
  apply backwardLog_stability _ _ _ (gridExponents_pos L)
  intro y
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (F-G) _

lemma reservoirTrialLog_lipschitz (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) : LipschitzWith 1 (fun F : (Fin a → Spin) → ℝ =>
      trialLog L (reservoirTrialLaw M C H N L u)
        (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog F)) := by
  apply LipschitzWith.of_dist_le_mul
  intro F G
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  apply trialLog_stability L _ _ (FiniteLaw.spinLog_continuous F) (FiniteLaw.spinLog_continuous G)
    (FiniteLaw.spinLog_bound F (fun s => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm F s))
    (FiniteLaw.spinLog_bound G (fun s => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm G s))
    (fun x => FiniteLaw.spinLog_stability F G (fun s => by
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (F-G) s) x)
    _ (fun i => gridExponents_pos L i.castSucc)
end DilutedSpinGlass.UniversalDictionary

end

end OAI
