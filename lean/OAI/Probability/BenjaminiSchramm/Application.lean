import OAI.Probability.BenjaminiSchramm.CayleyTheorem

namespace OAI

namespace Percolation.BenjaminiSchramm

open MeasureTheory

universe u v
variable {V : Type u} {E : Type v}

def OperatorConclusions (G : BondGraph V E) : Prop :=
  MainConclusion G ∧
  (∀ x, triangleDiagram G (pc G) x ≤ operatorNorm G (pc G) ^ 3 ∧
    triangleDiagram G (pc G) x < ⊤) ∧
  (pc G < ptwo G ∧ ptwo G ≤ pexp G) ∧
  ∀ p : unitInterval, p < ptwo G → ExponentialDecay G p

theorem operatorConclusions_of_main [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hm : MainConclusion G) : OperatorConclusions G := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  exact ⟨hm, critical_triangle_of_mainConclusion G hm,
    ⟨hm.2.2.1, ptwo_le_pexp G hconn hloc⟩,
    exponentialDecay_of_lt_ptwo G hconn hloc⟩

theorem operator_conclusions_conditional [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G)) : OperatorConclusions G :=
  operatorConclusions_of_main G hconn hloc (main_conditional G hconn hloc hqt hh hutchcroft2019)

theorem operator_conclusions_unimodular [Infinite V]
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) (huni : AutUnimodular G hG hconn hloc) : OperatorConclusions G :=
  operatorConclusions_of_main G hconn hloc (mainConclusion_of_critical_bounded G hconn hloc hqt
    (critical_bounded_of_unimodular G hG hconn hloc hqt hh huni))

theorem critical_laws_of_main [Infinite V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G) (hm : MainConclusion G)
    (hfirst : HutchcroftFirstMomentInput G)
    (htheta : TrianglePercolationProbabilityInput G)
    (hvolume : HutchcroftCriticalVolumeInput G)
    (hradii : HutchcroftCriticalRadiiInput G) : CriticalLawsConclusion G := by
  let : Countable V := countable_vertices hgraph.locallyFinite hgraph.connected
  let : Countable E := countable_edges hgraph.locallyFinite
  have hb := (operatorNorm_lt_top_iff G (pc G)).mp hm.2.1
  have hθ := percolationProbabilityLaw_of_publishedInput G hgraph htheta hb
  have hp1 : pc G < 1 := hm.2.2.1.trans_le (ptwo G).2.2
  have hfin := critical_finite_of_probabilityLaw G hp1 hθ
  exact ⟨critical_triangle_of_mainConclusion G hm,
    susceptibilityLaw_of_publishedInput G hgraph hfirst hm.2.2.1, hθ,
    criticalTailLaws_of_publishedInputs G hgraph hvolume hradii hm.2.2.1 hfin,
    ⟨hm.2.2.1,ptwo_le_pexp G hgraph.connected hgraph.locallyFinite⟩,
    exponentialDecay_of_lt_ptwo G hgraph.connected hgraph.locallyFinite⟩

theorem full_application_conditional [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G))
    (hfirst : HutchcroftFirstMomentInput (subdivision G))
    (htheta : TrianglePercolationProbabilityInput (subdivision G))
    (hvolume : HutchcroftCriticalVolumeInput (subdivision G))
    (hradii : HutchcroftCriticalRadiiInput (subdivision G)) :
    MainConclusion G ∧ CriticalLawsConclusion G := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  have hm := main_conditional G hconn hloc hqt hh hutchcroft2019
  have hmH := mainConclusion_of_critical_bounded (subdivision G)
    (subdivision_connected G hconn) (subdivision_locallyFinite G hloc)
    (subdivision_quasiTransitive G hloc hqt)
    (critical_subdivision_bounded_conditional G hconn hloc hqt hh hutchcroft2019)
  have hH := critical_laws_of_main (subdivision G)
    (publishedSimpleGraph_subdivision G hconn hloc hqt) hmH hfirst htheta hvolume hradii
  exact ⟨hm,critical_triangle_of_mainConclusion G hm,
    susceptibilityLaw_of_subdivision G hloc hqt hH.2.1,
    probabilityLaw_of_subdivision G hloc hqt hH.2.2.1,
    criticalTailLaws_of_subdivision G hloc hqt hH.2.2.2.1,
    ⟨hm.2.2.1,ptwo_le_pexp G hconn hloc⟩,
    exponentialDecay_of_lt_ptwo G hconn hloc⟩

theorem cayley_operator_conclusions
    {Λ : Type*} [Group Λ] (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : 1 ∉ S) (hgen : Subgroup.closure (S : Set Λ) = ⊤)
    (hna : ¬ FolnerAmenable Λ) : OperatorConclusions (cayleyBond S) := by
  let : Infinite Λ := infinite_of_not_folnerAmenable hna
  exact operatorConclusions_of_main (cayleyBond S) (cayleyBond_connected S hgen)
    (cayleyBond_locallyFinite S hsym) (cayley_main S hsym hone hgen hna).2.1

end Percolation.BenjaminiSchramm

end OAI
