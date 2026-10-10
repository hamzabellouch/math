import OAI.Probability.BenjaminiSchramm.GhostMomentDischarge
import OAI.Probability.BenjaminiSchramm.RadiusInputReduction

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem critical_operator_of_quarter_moments [Infinite V]
    (G : BondGraph V E) (hinj : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hmoment : ∀ x ∈ ((criticalModel G).orbitRepresentatives
        (criticalModel_quasiTransitive G hqt)).roots,
      (criticalModel G).quarterThreeQuarterMoment (pc G) x < ⊤) :
    OperatorBounded G (pc G) := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  have hpc1 : (pc G : ℝ) < 1 := pc_lt_one_of_nonamenable G hconn hloc hqt hh
  exact operatorBounded_of_finite_quarterTiltedSusceptibility G hconn hloc hqt (pc G)
    (finite_quarterSusceptibility_of_moments G hinj (criticalModel_connected G hconn) hloc
      (criticalModel_quasiTransitive G hqt) (pc G) hpc1
      (critical_finite_general G hconn hloc hqt hpc1) hmoment)

theorem strict_gap_of_quarter_moments [Infinite V]
    (G : BondGraph V E) (hinj : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hmoment : ∀ x ∈ ((criticalModel G).orbitRepresentatives
        (criticalModel_quasiTransitive G hqt)).roots,
      (criticalModel G).quarterThreeQuarterMoment (pc G) x < ⊤) :
    pc G < ptwo G := by
  exact (mainConclusion_of_critical_bounded G hconn hloc hqt
    (critical_operator_of_quarter_moments G hinj hconn hloc hqt hh hmoment)).2.2.1

end Percolation.BenjaminiSchramm

end OAI
