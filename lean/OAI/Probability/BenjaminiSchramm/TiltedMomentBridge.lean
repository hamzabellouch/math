import OAI.Probability.BenjaminiSchramm.TiltedMoments
import OAI.Probability.BenjaminiSchramm.TiltedGhostSusceptibility
import OAI.Probability.BenjaminiSchramm.CriticalFiniteness

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def modularHeight (G : BondGraph V E) (o x : V) : ℝ :=
  Real.log ((criticalModel G).modularRatio x o)

theorem quarterTiltedMass_eq_logarithmic_mass [Nonempty V]
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G) (ω : Set E) (o : V) :
    (criticalModel G).quarterTiltedMass ω o =
      quarterTiltedClusterMass G (modularHeight G o) ω o := by
  unfold CriticalPercolation.BondGraph.quarterTiltedMass quarterTiltedClusterMass
  apply tsum_congr
  intro x
  have hr : ((criticalModel G).openGraph ω).Reachable o x ↔ Conn G ω o x := by
    rw [criticalModel_openGraph]
    exact (conn_iff_reachable G ω o x).symm
  rw [hr]
  split_ifs
  · have hpos := (criticalModel G).modularRatio_pos (criticalModel_connected G hc) hl x o
    rw [CriticalPercolation.BondGraph.stabilizerWeight, ENNReal.ofReal_rpow_of_pos hpos,
      Real.rpow_def_of_pos hpos]
    congr 2
    dsimp [modularHeight]
    ring
  · rfl

theorem quarterTiltedMass_moment_lt_top_of_layers [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (p : unitInterval) (o : V) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ k : ℤ, 0 ≤ k →
      (∫⁻ ω, modularLayerCount G (modularHeight G o) ω o k ^ (3 / 4 : ℝ) ∂law p) ≤
        ENNReal.ofReal (C * Real.exp (-(k : ℝ) / 2)))
    (hneg : ∀ k : ℤ, k ≤ 0 →
      (∫⁻ ω, modularLayerCount G (modularHeight G o) ω o k ^ (3 / 4 : ℝ) ∂law p) ≤
        ENNReal.ofReal (C * Real.exp (-(k : ℝ) / 16))) :
    (∫⁻ ω, (criticalModel G).quarterTiltedMass ω o ^ (3 / 4 : ℝ)
      ∂(criticalModel G).law p) < ⊤ := by
  simp_rw [quarterTiltedMass_eq_logarithmic_mass G hc hl]
  exact quarterTilted_moment_lt_top_of_layer_bounds G p (modularHeight G o) o C hC hpos hneg

end Percolation.BenjaminiSchramm

end OAI
