import OAI.Probability.UnimodularPercolation.Main

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v} [Infinite V]

theorem critical_subdivision_bounded_conditional
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G)) :
    OperatorBounded (subdivision G) (pc (subdivision G)) := by
  classical
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  by_cases huni : AutUnimodular (subdivision G) (subdivision_injective G)
      (subdivision_connected G hconn) (subdivision_locallyFinite G hloc)
  · exact critical_bounded_of_unimodular (subdivision G) (subdivision_injective G)
      (subdivision_connected G hconn) (subdivision_locallyFinite G hloc)
      (subdivision_quasiTransitive G hloc hqt) (subdivision_hV_pos G hloc hqt hh) huni
  · obtain ⟨q, hq, hpq⟩ := lt_sSup_iff.mp (hutchcroft2019 huni)
    exact operatorBounded_of_le (subdivision G) hpq.le hq

theorem critical_bounded_conditional
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G)) :
    OperatorBounded G (pc G) := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  exact critical_bounded_of_subdivision G hloc
    (critical_subdivision_bounded_conditional G hconn hloc hqt hh hutchcroft2019)

theorem main_conditional
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G)) :
    MainConclusion G :=
  mainConclusion_of_critical_bounded G hconn hloc hqt
    (critical_bounded_conditional G hconn hloc hqt hh hutchcroft2019)

end Percolation.BenjaminiSchramm

end OAI
