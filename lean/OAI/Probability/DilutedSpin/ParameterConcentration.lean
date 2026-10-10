import OAI.Probability.DilutedSpin.ConcentrationRate
import OAI.Probability.DilutedSpin.SingletonRoot

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks Set
open scoped NNReal ENNReal BigOperators
variable {X Y I J : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [DecidableEq J]
  {A : I → Type} [∀ i, Fintype (A i)] {N L : ℕ}

/-- Concentration averaged over the literal infinite dictionary parameter law.
All other coordinates remain fixed during the one-coordinate estimate. -/
theorem spin_parameter_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hVm : ∀ σ, Measurable (fun x => V x σ)) (hhm : Measurable field)
    {C H c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hV : ∀ x σ, |V x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ l, c ≤ m l)
    (key : I → J) (a b t : J → ℝ) (hab : ∀ j, a j < b j)
    (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4)) (ht : ∀ j, |t j| ≤ 1/4)
    (D E : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (j : J) {ρ : ℝ} (hρ : 0 < ρ)
    (hJ : Icc (a j-ρ) (b j+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let T := KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L
    let base := fun h k (x : RootPath X k) z => energy V field h k x (KernelTower.terminalState L z)
    (∫ u, parameterError (fun _ : Fin N => ξ) μ ν r s T Q m base key a b t D E j u
      ∂Measure.infinitePi (fun j => intervalParameterLaw (a j) (b j))) ≤
      Real.sqrt ((b j-a j)*(4+4*(b j-a j))/c*(s:ℝ))/(b j-a j)+
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+2*H^2*N)/ρ+
      12*ρ*(s:ℝ)/(b j-a j)+Real.sqrt s := by
  dsimp only
  let T := KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L
  let base := fun h k (x : RootPath X k) z => energy V field h k x (KernelTower.terminalState L z)
  let π := Measure.infinitePi (fun j => intervalParameterLaw (a j) (b j))
  let (j : J) : IsProbabilityMeasure (intervalParameterLaw (a j) (b j)) :=
    intervalParameterLaw_probability (hab j)
  have hb := fun k z => measurable_energy V field hVm hhm k (KernelTower.terminalState L z)
  apply parameter_average_le a b hab j
    (parameterError (fun _ : Fin N => ξ) μ ν r s T Q m base key a b t D E j)
    (measurable_parameterError _ μ ν r s T Q m base key a b t D E hb j)
    (integrable_parameterError _ μ ν r s T Q m base key a b t D E π hb
      (fun j => (hab j).le) hI ht hD hE j)
  intro u
  have heq := intervalIntegral.integral_congr (μ := volume) (a := a j) (b := b j)
    (f := fun v => parameterError (fun _ : Fin N => ξ) μ ν r s T Q m base key a b t D E j (Function.update u j v))
    (g := fun v => fullSelectedError (fun _ : Fin N => ξ) μ ν r s T Q m base
      (fun i => decide (key i = j)) (parameterFactor key a b t D E u) D E (t j) v)
    (fun v hv => parameterError_refresh _ μ ν r s T Q m base key a b t D E j u
      (by simpa only [uIcc_of_le (hab j).le] using hv))
  rw [heq]
  exact spin_selected_concentration μ ν ξ r s V field hVm hhm hC hc hV hh Q m hm
    (fun i => decide (key i = j)) (parameterFactor key a b t D E u) D E
    (parameterFactor_log_bound key a b t (fun j => (hab j).le) hI ht D E hD hE u)
    hD hE (ht j) (hab j) hρ hJ

end DilutedSpinGlass.PhysicalRoot
end

end

end OAI
