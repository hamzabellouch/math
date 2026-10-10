import OAI.Probability.BenjaminiSchramm.SubdivisionConsequences
import OAI.Probability.BenjaminiSchramm.SubdivisionOperator

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem publishedSimpleGraph_subdivision (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) :
    PublishedSimpleGraph (subdivision G) := by
  refine ⟨subdivision_injective G, ?_, subdivision_connected G hconn,
    subdivision_locallyFinite G hloc, subdivision_quasiTransitive G hloc hqt⟩
  intro e x hx
  exact subdivision_loopless G x ⟨e, hx⟩

theorem exponentialDecay_of_subdivision [Countable V] [Countable E]
    (G : BondGraph V E) (q : unitInterval)
    (h : ExponentialDecay (subdivision G) q) : ExponentialDecay G (q ^ 2) := by
  obtain ⟨A, a, hA, ha, hb⟩ := h
  refine ⟨A, 2 * a, hA, by positivity, ?_⟩
  intro x y
  have hh := hb (.inl x) (.inl y)
  rw [twoPoint_subdivision, graphDistance_subdivision] at hh
  convert hh using 1
  congr 2
  push_cast
  ring

theorem full_conditional [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G))
    (hfirst : HutchcroftFirstMomentInput (subdivision G))
    (htheta : TrianglePercolationProbabilityInput (subdivision G))
    (hvolume : HutchcroftCriticalVolumeInput (subdivision G))
    (hradii : HutchcroftCriticalRadiiInput (subdivision G))
    (hexp : HutchcroftExponentialInput (subdivision G)) :
    MainConclusion G ∧ CriticalLawsConclusion G := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  have hHconn := subdivision_connected G hconn
  have hHloc := subdivision_locallyFinite G hloc
  have hHqt := subdivision_quasiTransitive G hloc hqt
  have hmain := main_conditional G hconn hloc hqt hh hutchcroft2019
  have hmainH := mainConclusion_of_critical_bounded (subdivision G) hHconn hHloc hHqt
    (critical_subdivision_bounded_conditional G hconn hloc hqt hh hutchcroft2019)
  have hlaws := critical_laws_of_mainConclusion (subdivision G)
    (publishedSimpleGraph_subdivision G hconn hloc hqt) hmainH
    hfirst htheta hvolume hradii hexp
  have hdecay (p : unitInterval) (hp : p < ptwo G) : ExponentialDecay G p := by
    let q := squareParameter.symm p
    have hq2 : q ^ 2 = p := squareParameter.apply_symm_apply p
    have hq : q < ptwo (subdivision G) := by
      apply squareParameter.lt_iff_lt.mp
      change q ^ 2 < ptwo (subdivision G) ^ 2
      rw [ptwo_subdivision_sq G hloc hqt, hq2]
      exact hp
    simpa only [hq2] using exponentialDecay_of_subdivision G q (hlaws.2.2.2.2.2 q hq)
  refine ⟨hmain, critical_triangle_of_mainConclusion G hmain,
    susceptibilityLaw_of_subdivision G hloc hqt hlaws.2.1,
    probabilityLaw_of_subdivision G hloc hqt hlaws.2.2.1,
    criticalTailLaws_of_subdivision G hloc hqt hlaws.2.2.2.1,
    ⟨hmain.2.2.1, ?_⟩, hdecay⟩
  apply le_of_forall_lt_imp_le_of_dense
  intro p hp
  exact le_sSup (hdecay p hp)

end Percolation.BenjaminiSchramm

end OAI
