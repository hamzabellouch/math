import OAI.Probability.BenjaminiSchramm.CriticalQuarterMoment
import OAI.Probability.BenjaminiSchramm.NonunimodularMomentReduction
import OAI.Probability.BenjaminiSchramm.CombinatorialUnimodularOperator

namespace OAI

namespace Percolation.BenjaminiSchramm
universe u v
variable {V : Type u} {E : Type v} [Infinite V]

theorem simple_critical_bounded
    (G : BondGraph V E) (hinj : Function.Injective G)
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hh : 0 < hV G) : OperatorBounded G (pc G) := by
  classical
  let : Countable V := countable_vertices hl hc
  let : Countable E := countable_edges hl
  by_cases hu : (criticalModel G).CombinatoriallyUnimodular
  · exact critical_bounded_of_combinatorial_unimodular G hinj hc hl hq hh hu
  · exact critical_operator_of_quarter_moments G hinj hc hl hq hh
      (fun x _hx => critical_quarter_moment_finite G hc hl hq
        (by exact_mod_cast pc_lt_one_of_nonamenable G hc hl hq hh) hu x)

theorem simple_strict_gap
    (G : BondGraph V E) (hinj : Function.Injective G)
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hh : 0 < hV G) : pc G < ptwo G :=
  (mainConclusion_of_critical_bounded G hc hl hq
    (simple_critical_bounded G hinj hc hl hq hh)).2.2.1

theorem subdivision_gap_input_proved
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) :
    ¬ AutUnimodular (subdivision G) (subdivision_injective G)
      (subdivision_connected G hc) (subdivision_locallyFinite G hl) →
    pc (subdivision G) < ptwo (subdivision G) := by
  intro _hu
  exact simple_strict_gap (subdivision G) (subdivision_injective G)
    (subdivision_connected G hc) (subdivision_locallyFinite G hl)
    (subdivision_quasiTransitive G hl hq) (subdivision_hV_pos G hl hq hh)

end Percolation.BenjaminiSchramm

end OAI
