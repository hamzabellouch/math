import OAI.Probability.BenjaminiSchramm.CriticalPeakComparison
import OAI.Probability.BenjaminiSchramm.RestrictedMomentHolder

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma mixedHeightLayerMoment_eq_lintegral (a : V → ℝ) (p : unitInterval)
    (d c l u ad t : ℝ) (x : V) :
    G.mixedHeightLayerMoment a p d c l u ad t x =
      ∫⁻ ω, (restrictedHit G.ends
        (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a x z}) x
        {z | t ≤ G.orbitAdjustedHeight a x z})ᶜ.indicator
      (fun ω => restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c})
        {z | l ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u} ω x) ω ∂G.law p := by
  let D := Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a x z}
  let I := Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}
  let W : Set V := {z | l ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u}
  let P := (restrictedHit G.ends D x {z | t ≤ G.orbitAdjustedHeight a x z})ᶜ
  change G.mixedHeightLayerMoment a p d c l u ad t x =
    ∫⁻ ω, P.indicator (fun ω => restrictedLayerCount G.ends I W ω x) ω ∂Percolation.law p
  rw [lintegral_indicator_restrictedLayerCount G.ends p P
    (measurableSet_restrictedHit G.ends D x _).compl I W x]
  unfold mixedHeightLayerMoment
  apply tsum_congr
  intro y
  by_cases hy : l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u
  · simp only [W,Set.mem_ofPred_eq,hy]
    apply congrArg (Percolation.law p)
    ext ω
    exact and_comm
  · simp only [W,Set.mem_ofPred_eq,hy,ite_false]

end CriticalPercolation.BondGraph

end

end OAI
