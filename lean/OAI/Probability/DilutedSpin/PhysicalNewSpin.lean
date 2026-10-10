import OAI.Probability.DilutedSpin.TerminalMeanField

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I Y : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] {A : I → Type} [∀ i,Fintype (A i)] {N k p L : ℕ} [NeZero N]

lemma newSpin_field_marginal
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (E : (Fin N → Spin) → ℝ)
    (θ : Fin k → InteractionSample p) (j : Fin k × Fin (p-1) → Fin N)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    (∫ h,terminalMean ν s Q m ψ Fin.succ
      ((fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+
          ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0)))+fieldEnergy field h)
        ∂rootLaw (N+1) (fun _ => ξ)) =
      ∫ h,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)
        (fun σ => E σ+cavitySiteEnergy θ (field h) (fun a => σ (j a))) ∂ξ := by
  rw [show rootLaw (N+1) (fun _ => ξ)=ξ.prod (rootLaw N (fun _ => ξ)) from rfl]
  rw [integral_prod _ (terminalMean_field_integrable ξ ν s Q m hm ψ field hhm Fin.succ _ hH hh hf)]
  apply integral_congr_ae
  filter_upwards [] with h
  rw [averagedEnergyRoot_eq_terminalMean]
  apply integral_congr_ae
  filter_upwards [] with h'
  have he : ((fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+
      ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0)))+fieldEnergy field (h,h')) =
      (fun σ => (E+fieldEnergy field h') (fun i => σ i.succ)+field h*spin (σ 0)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) := by
    funext σ
    simp only [Pi.add_apply,fieldEnergy_cons]
    ring
  rw [he,terminalMean_cavity_marginal ν s Q m hend]
  congr 1
  funext σ
  change (E σ+fieldEnergy field h' σ)+_=(E σ+_)+fieldEnergy field h' σ
  ring

/-- Removing marks on the new site and then summing out that spin gives the
actual cavity-site root, with precisely the O(s/N) projection error. -/
lemma averagedEnergyRoot_newSpin
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (E : (Fin N → Spin) → ℝ)
    (θ : Fin k → InteractionSample p) (j : Fin k × Fin (p-1) → Fin N)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
      (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
      (fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) -
      (∫ h,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)
        (fun σ => E σ+cavitySiteEnergy θ (field h) (fun a => σ (j a))) ∂ξ)|≤2*D*s/(N+1) := by
  rw [← newSpin_field_marginal ξ ν s Q m hm hend ψ field hhm E θ j hH hh hf]
  exact averagedEnergyRoot_mark_projection ξ ν s Q m hm ψ field hhm _ hH hh hf

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
