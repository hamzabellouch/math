import OAI.Probability.BenjaminiSchramm.CriticalFiniteness
import OAI.Probability.BenjaminiSchramm.TiltedSusceptibility
import OAI.Probability.BenjaminiSchramm.Nonunimodular

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem criticalModel_connectionMeasure (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (criticalModel G).connectionMeasure p x y = ENNReal.ofReal (twoPoint G p x y) := by
  unfold CriticalPercolation.BondGraph.connectionMeasure
  have he : {ω | ((criticalModel G).openGraph ω).Reachable x y} =
      {ω | Conn G ω x y} := by
    ext ω
    change ((criticalModel G).openGraph ω).Reachable x y ↔ Conn G ω x y
    rw [criticalModel_openGraph]
    exact (conn_iff_reachable G ω x y).symm
  rw [he]
  exact (ENNReal.ofReal_toReal (measure_ne_top (law p) _)).symm

theorem modularSqrtWeight_ratio
    (G : CriticalPercolation.BondGraph V E) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x y : V) :
    Real.sqrt (G.modularRatio y o) / Real.sqrt (G.modularRatio x o) =
      Real.sqrt (G.modularRatio y x) := by
  rw [← G.modularRatio_cocycle hc hl y x o,
    Real.sqrt_mul (G.modularRatio_pos hc hl y x).le]
  exact mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr (G.modularRatio_pos hc hl x o)).ne'

theorem modularSqrtWeight_ratio_ofReal
    (G : CriticalPercolation.BondGraph V E) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x y : V) :
    ENNReal.ofReal (Real.sqrt (G.modularRatio y o) / Real.sqrt (G.modularRatio x o)) =
      G.stabilizerWeight x y ^ (1 / 2 : ℝ) := by
  rw [modularSqrtWeight_ratio G hc hl, CriticalPercolation.BondGraph.stabilizerWeight,
    ENNReal.ofReal_rpow_of_pos (G.modularRatio_pos hc hl y x), ← Real.sqrt_eq_rpow]

theorem operatorBounded_of_finite_halfTiltedSusceptibility [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (p : unitInterval)
    (C : ℝ≥0∞) (hC : C < ∞)
    (hb : ∀ x, (criticalModel G).tiltedSusceptibility p (1 / 2) x ≤ C) :
    OperatorBounded G p := by
  let H := criticalModel G
  have hc := criticalModel_connected G hconn
  let o : V := Classical.choice inferInstance
  let w (x : V) := Real.sqrt (H.modularRatio x o)
  have hw (x : V) : 0 < w x := Real.sqrt_pos.mpr (H.modularRatio_pos hc hloc x o)
  apply operatorBounded_of_weighted_susceptibility G p w C.toReal hw ENNReal.toReal_nonneg
  intro x s
  have ht (y : V) :
      ENNReal.ofReal (twoPoint G p x y * w y / w x) =
        H.connectionMeasure p x y * H.stabilizerWeight x y ^ (1 / 2 : ℝ) := by
    rw [mul_div_assoc, ENNReal.ofReal_mul (twoPoint_nonneg G p x y),
      ← criticalModel_connectionMeasure, modularSqrtWeight_ratio_ofReal H hc hloc]
  have hn (y : V) : 0 ≤ twoPoint G p x y * w y / w x :=
    div_nonneg (mul_nonneg (twoPoint_nonneg G p x y) (hw y).le) (hw x).le
  have hs : ENNReal.ofReal (∑ y ∈ s, twoPoint G p x y * w y / w x) ≤ C := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => hn y)]
    simp_rw [ht]
    exact (ENNReal.sum_le_tsum s).trans (hb x)
  have hr := ENNReal.toReal_mono hC.ne hs
  rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun y _ => hn y))] at hr

theorem operatorBounded_of_finite_quarterTiltedSusceptibility [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval)
    (hfin : ∀ x ∈ ((criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hqt)).roots,
      (criticalModel G).tiltedSusceptibility p (1 / 4) x < ∞) :
    OperatorBounded G p := by
  let : Countable V := countable_vertices hloc hconn
  obtain ⟨C,hC,hb⟩ := (criticalModel G).uniform_halfTiltedSusceptibility_of_quarter
    (criticalModel_connected G hconn) hloc (criticalModel_quasiTransitive G hqt) p hfin
  exact operatorBounded_of_finite_halfTiltedSusceptibility G hconn hloc p C hC hb

end Percolation.BenjaminiSchramm

end OAI
