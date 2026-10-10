import OAI.Probability.DilutedSpin.TerminalInterior

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open ConcreteReservoir UniversalDictionary HeterogeneousMarks KernelTower
open scoped BigOperators
noncomputable local instance (β : Type) : DecidableEq β := Classical.decEq β

lemma uniform_spinMean_hypotheses {N : ℕ} (hN : 0<N) (i : Site N) :
    (∃ σ : Fin N → Spin, 0<(FiniteLaw.uniform : FiniteLaw (Fin N → Spin)).weight σ ∧
      spin (readSpin σ i)<1) ∧
    (∃ σ : Fin N → Spin, 0<(FiniteLaw.uniform : FiniteLaw (Fin N → Spin)).weight σ ∧
      -1<spin (readSpin σ i)) := by
  have hw (σ : Fin N → Spin) : 0<(FiniteLaw.uniform : FiniteLaw (Fin N → Spin)).weight σ := by
    simp only [FiniteLaw.uniform]
    positivity
  constructor
  · refine ⟨fun _ => false,hw _,?_⟩
    rw [readSpin_eq hN]
    norm_num [spin]
  · refine ⟨fun _ => true,hw _,?_⟩
    rw [readSpin_eq hN]
    norm_num [spin]

lemma terminalInterior_rootTower {N r : ℕ} (hN : 0<N)
    {I X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)] {M : ℕ}
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath (Fin N → Spin) (r+1) → ℝ)
    (old : (i : I) → FinitePath (Fin N → Spin) (r+1) → FinitePath (A i) (r+1) → ℝ)
    (z : FullRootState Y X I M) (i : Site N) :
    TerminalInterior r
      (rootTower (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m base old z)
      (fun y => rootVector (readVector (fun v x => readSpin (terminalState r x) v)) z y i) := by
  obtain ⟨hl,hu⟩ := uniform_spinMean_hypotheses hN i
  exact terminalInterior_tilted r (rootArray z.2.2.1 z.2.2.2) FiniteLaw.uniform
    (fun _ : Fin N => false) Q m _ (fun σ => spin (readSpin σ i))
    (fun σ => (abs_spin _).le) hl hu

end DilutedSpinGlass.PhysicalRoot

end

end OAI
