import OAI.Probability.DilutedSpin.GlobalSelectedConcentration
import OAI.Probability.DilutedSpin.SpinRootData

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks Set
open scoped NNReal ENNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)] {N L : ℕ}

/-- The concentration envelope for the actual bounded physical spin energy,
with all heterogeneous dictionary marks retained. -/
theorem spin_selected_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hVm : ∀ σ, Measurable (fun x => V x σ)) (hhm : Measurable field)
    {C H c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hV : ∀ x σ, |V x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j, c ≤ m j)
    (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let T := KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L
    let base := fun h k (x : RootPath X k) z => energy V field h k x (KernelTower.terminalState L z)
    (∫ u in a..b, fullSelectedError (fun _ : Fin N => ξ) μ ν r s T Q m base sel fixed D E t u)/(b-a) ≤
      Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ))/(b-a)+
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+2*H^2*N)/ρ+
      12*ρ*(s:ℝ)/(b-a)+Real.sqrt s := by
  dsimp only
  have h := full_selected_error_concentration μ ν (fun _ : Fin N => ξ) r s
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m hc hm
    (fun h k x z => energy V field h k x (KernelTower.terminalState L z))
    (fun k z => measurable_energy V field hVm hhm k (KernelTower.terminalState L z))
    sel fixed D E hC
    (fun h k x z => energy_bound V field hV hh h k x (KernelTower.terminalState L z)) hf hD hE
    (fun h k j x z w => energy_replace_interaction V field hV h k j x z (KernelTower.terminalState L w))
    (fun h k z x w => energy_add_interaction V field hV h k z x (KernelTower.terminalState L w))
    (fun _ => 2*H)
    (fun j h z k x w => energy_replace_field V field hh h j z k x (KernelTower.terminalState L w))
    ht hab hρ hJ
  have hfieldSum : (∑ _ : Fin N, (2*H)^2/2) = 2*H^2*N := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simpa only [hfieldSum] using h

end DilutedSpinGlass.PhysicalRoot
end

end

end OAI
