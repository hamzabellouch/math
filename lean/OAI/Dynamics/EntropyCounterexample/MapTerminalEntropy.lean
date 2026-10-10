import OAI.Dynamics.EntropyCounterexample.MapInfinity
import OAI.Dynamics.EntropyCounterexample.RawInvariantSets
import OAI.Dynamics.EntropyCounterexample.SaturationEntropy
import OAI.Dynamics.EntropyCounterexample.EntropyLocalization

namespace OAI

noncomputable section

namespace Problem340.Construction.TerminalEntropy

open RawInvariantSets

def registers (L : ℝ) (hL : 2 < L) : (Fin 3 → Sphere) → (Fin 3 → Sphere) :=
  registerMap (fun z => (L : ℂ) * (concreteData L hL).saturation z)

theorem zero_semiconj (L : ℝ) (hL : 2 < L) :
    Function.Semiconj (zeroSlice ((50 : ℝ) : AddCircle (100 : ℝ)))
      (registers L hL) (concreteMap L hL) := by
  intro v
  exact (concreteMap_fifty_zero L hL v).symm

def terminalSet : Set RawManifold :=
  zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ)) ∪ rawInfinitySet 3

theorem terminalSet_nonempty : terminalSet.Nonempty :=
  (zeroSet_nonempty 3 ((50 : ℝ) : AddCircle (100 : ℝ))).mono Set.subset_union_left

theorem isCompact_terminalSet : IsCompact terminalSet :=
  (isCompact_zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ))).union
    (isCompact_rawInfinitySet 3)

theorem concreteMap_mapsTo_zero (L : ℝ) (hL : 2 < L) :
    Set.MapsTo (concreteMap L hL)
      (zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ)))
      (zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ))) := by
  rintro x ⟨v, rfl⟩
  exact ⟨registers L hL v, zero_semiconj L hL v⟩

theorem concreteMap_mapsTo_terminal (L : ℝ) (hL : 2 < L) :
    Set.MapsTo (concreteMap L hL) terminalSet terminalSet := by
  intro x hx
  rcases hx with hz | hi
  · exact Or.inl (concreteMap_mapsTo_zero L hL hz)
  · exact Or.inr (concreteMap_mapsTo_infinitySet L hL hi)

theorem coverEntropy_zero_image (L : ℝ) (hL : 2 < L)
    {X : Type*} [UniformSpace X] {T : X → X}
    {φ : RawManifold → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ (concreteMap L hL) T) :
    Dynamics.coverEntropy T
      (φ '' zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ))) = 0 := by
  let : UniformSpace (OnePoint ℂ) := uniformSpaceOfCompactR1
  have hregisters : Dynamics.coverEntropy (registers L hL) Set.univ = 0 := by
    have h := SaturationEntropy.coverEntropy_onePoint_saturation L (by linarith) 3
    have heq : registers L hL = RadialRegisterEntropy.coordinatewise
        (fun x : OnePoint ℂ => ((L • sphereSaturation (3 * L) (by linarith) x : ℂ) :
          OnePoint ℂ)) 3 := by
      funext v i
      exact congrArg ((↑) : ℂ → OnePoint ℂ) Complex.real_smul.symm
    rw [heq]
    exact h
  let ψ : (Fin 3 → Sphere) → X :=
    φ ∘ zeroSlice ((50 : ℝ) : AddCircle (100 : ℝ))
  have hψ : Continuous ψ := hφ.comp (continuous_zeroSlice _)
  have hs : Function.Semiconj ψ (registers L hL) T := by
    intro v
    exact (congrArg φ (zero_semiconj L hL v)).trans
      (hsem (zeroSlice ((50 : ℝ) : AddCircle (100 : ℝ)) v))
  have hrange : Set.range ψ =
      φ '' zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ)) := by
    exact Set.range_comp _ _
  rw [← hrange]
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg T (Set.range_nonempty ψ))
  have h := Dynamics.coverEntropy_image_le_of_uniformContinuous hs
    (CompactSpace.uniformContinuous_of_continuous hψ) Set.univ
  simpa only [Set.image_univ, hregisters] using h

theorem coverEntropy_terminal_image (L : ℝ) (hL : 2 < L)
    {X : Type*} [UniformSpace X] {T : X → X}
    {φ : RawManifold → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ (concreteMap L hL) T) :
    Dynamics.coverEntropy T (φ '' terminalSet) = 0 := by
  rw [terminalSet, Set.image_union, Dynamics.coverEntropy_union,
    coverEntropy_zero_image L hL hφ hsem,
    coverEntropy_concreteInfinity_image L hL hφ hsem, max_self]

theorem mapsTo_terminal_image (L : ℝ) (hL : 2 < L)
    {X : Type*} {T : X → X} {φ : RawManifold → X}
    (hsem : Function.Semiconj φ (concreteMap L hL) T) :
    Set.MapsTo T (φ '' terminalSet) (φ '' terminalSet) := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨concreteMap L hL y, concreteMap_mapsTo_terminal L hL hy, hsem y⟩

theorem coverEntropy_eq_zero_of_terminal_attraction (L : ℝ) (hL : 2 < L)
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X] {T : X → X}
    (hT : Continuous T) {φ : RawManifold → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ (concreteMap L hL) T)
    (hattract : ∀ x, Filter.Tendsto
      (fun n => Metric.infDist (T^[n] x) (φ '' terminalSet))
      Filter.atTop (nhds 0)) :
    Dynamics.coverEntropy T Set.univ = 0 := by
  exact Problem340.coverEntropy_eq_zero_of_pointwise_attraction hT
    (isCompact_terminalSet.image hφ) (terminalSet_nonempty.image φ)
    (mapsTo_terminal_image L hL hsem)
    (coverEntropy_terminal_image L hL hφ hsem) hattract

end Problem340.Construction.TerminalEntropy

end

end OAI
