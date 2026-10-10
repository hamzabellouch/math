import OAI.Probability.BenjaminiSchramm.ConsistentLayers
import OAI.Probability.BenjaminiSchramm.SlabLastMaximum

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedUpLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval)
    (n : ℕ) (x : V) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, restrictedLayerCount G.ends
    (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v ≤ (n : ℤ)})
    {v | G.adjustedLayerIndex a R u x v = (n : ℤ)} ω x ∂G.law p

def adjustedDownLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval)
    (n : ℕ) (x : V) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, restrictedLayerCount G.ends
    (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v ≤ 0})
    {v | G.adjustedLayerIndex a R u x v = -(n : ℤ)} ω x ∂G.law p

def supAdjustedUpLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ⨆ x, ⨆ u, G.adjustedUpLayerMoment a R p n x u

def infAdjustedUpLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ⨅ x, ⨅ u, G.adjustedUpLayerMoment a R p n x u

def supAdjustedDownLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ⨆ x, ⨆ u, G.adjustedDownLayerMoment a R p n x u

def infAdjustedDownLayerMoment (a : V → ℝ) (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ⨅ x, ⨅ u, G.adjustedDownLayerMoment a R p n x u

lemma adjustedUpLayerMoment_le_sup (a : V → ℝ) (R : ℝ) (p : unitInterval)
    (n : ℕ) (x : V) (u : ℝ) :
    G.adjustedUpLayerMoment a R p n x u ≤ G.supAdjustedUpLayerMoment a R p n :=
  le_iSup_of_le x (le_iSup_of_le u le_rfl)

lemma adjustedDownLayerMoment_le_sup (a : V → ℝ) (R : ℝ) (p : unitInterval)
    (n : ℕ) (x : V) (u : ℝ) :
    G.adjustedDownLayerMoment a R p n x u ≤ G.supAdjustedDownLayerMoment a R p n :=
  le_iSup_of_le x (le_iSup_of_le u le_rfl)

lemma adjustedUpLayerMoment_zero_ge_one [Countable V] [Countable E]
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (x : V) (u : ℝ) :
    1 ≤ G.adjustedUpLayerMoment a R p 0 x u := by
  have hh (ω : Set E) : (1 : ℝ≥0∞) ≤ restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v ≤ (0 : ℤ)})
      {v | G.adjustedLayerIndex a R u x v = (0 : ℤ)} ω x := by
    apply le_trans _ (ENNReal.le_tsum x)
    simp only [G.adjustedLayerIndex_self,Set.mem_ofPred_eq,
      Percolation.conn_refl,true_and,ite_true,le_refl]
  exact (show (1 : ℝ≥0∞) = ∫⁻ _ω : Set E, (1 : ℝ≥0∞) ∂G.law p by simp).le.trans
    (lintegral_mono hh)

end CriticalPercolation.BondGraph

end

end OAI
