import OAI.Probability.BenjaminiSchramm.UnconditionalInputs

namespace OAI

namespace Percolation.BenjaminiSchramm
universe u v
variable {V : Type u} {E : Type v} [Infinite V]

theorem full_main
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) : MainConclusion G :=
  main_conditional G hc hl hq hh (subdivision_gap_input_proved G hc hl hq hh)

theorem critical_laws
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) : CriticalLawsConclusion G :=
  (full_application_gap G hc hl hq hh (subdivision_gap_input_proved G hc hl hq hh)).2

theorem full_main_and_critical_laws
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) : MainConclusion G ∧ CriticalLawsConclusion G :=
  ⟨full_main G hc hl hq hh,critical_laws G hc hl hq hh⟩

theorem critical_bounded_unconditional
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) : OperatorBounded G (pc G) :=
  critical_bounded_conditional G hc hl hq hh (subdivision_gap_input_proved G hc hl hq hh)

end Percolation.BenjaminiSchramm

end OAI
