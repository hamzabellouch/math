import OAI.Probability.DilutedSpin.PhysicalNewSpin

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {Y I : Type} [MeasurableSpace Y] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

lemma averagedEnergyRoot_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (E : (Fin N → Spin) → ℝ) :
    |averagedEnergyRoot ξ ν s Q m field factor E|≤‖E‖+H*N+D*s := by
  have := rootLawProbability N (fun _ => ξ)
  exact abs_integral_le_bound (fun h => energyRoot_marks_bound ν s Q m hm field factor hh hf h E)

lemma cavitySiteEnergy_norm_bound {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (j : Fin k×Fin (p-1) → Fin N) (E : (Fin N → Spin) → ℝ)
    {C H : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hθ : ∀ a,‖(θ a).1‖≤C) (hh : |h|≤H) :
    ‖(fun σ => E σ+cavitySiteEnergy θ h (fun a => σ (j a)))‖≤‖E‖+H+C*k := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro σ
  rw [Real.norm_eq_abs]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ ‖E‖+(|h|+∑ a,‖(θ a).1‖) := add_le_add (norm_le_pi_norm E σ) (cavitySiteEnergy_bound θ h _)
    _ ≤ ‖E‖+(H+∑ _a : Fin k,C) := add_le_add_right (add_le_add hh (Finset.sum_le_sum (fun a _ => hθ a))) _
    _ = _ := by simp [mul_comm,add_assoc]

end DilutedSpinGlass.PhysicalRoot

end

end OAI
