import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakAddLemmas
import OAI.Geometry.NodalSets.Elliptic.RealJetProductExpansion

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis
open scoped ContDiff
noncomputable section

def realWeakJetProductSum (A : Jets.Coord → ℝ) (U : List (Fin 4) → Jets.Coord → ℝ)
    (ts : List (List (Fin 4) × List (Fin 4))) (x : Jets.Coord) : ℝ :=
  (ts.map (fun t ↦ partialJet A t.1 x*U t.2 x)).sum

lemma realWeakJetProductSum_append (A : Jets.Coord → ℝ) (U : List (Fin 4) → Jets.Coord → ℝ)
    (ts ss : List (List (Fin 4) × List (Fin 4))) (x : Jets.Coord) :
    realWeakJetProductSum A U (ts++ss) x = realWeakJetProductSum A U ts x+realWeakJetProductSum A U ss x := by
  simp [realWeakJetProductSum]

theorem real_weak_jet_product_derivative {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (U : List (Fin 4) → Jets.Coord → ℝ)
    (ts : List (List (Fin 4) × List (Fin 4))) (i : Fin 4)
    (hU : ∀ t ∈ ts, MemLp (U t.2) 2 (volume.restrict Q))
    (hD : ∀ t ∈ ts, MemLp (U (i::t.2)) 2 (volume.restrict Q))
    (hweak : ∀ t ∈ ts, ∀ psi : Jets.Coord → ℝ,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U t.2 x*coordPartial psi x i)=-(∫ x in Q, U (i::t.2) x*psi x)) :
    let V := realWeakJetProductSum A U ts
    let D := realWeakJetProductSum A U
      (ts.map (fun t ↦ (i::t.1,t.2)) ++ ts.map (fun t ↦ (t.1,i::t.2)))
    MemLp V 2 (volume.restrict Q) ∧ MemLp D 2 (volume.restrict Q) ∧
    ∀ psi : Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      IntegrableOn (fun x ↦ V x*coordPartial psi x i) Q ∧
      IntegrableOn (fun x ↦ D x*psi x) Q ∧
      (∫ x in Q, V x*coordPartial psi x i)=-(∫ x in Q, D x*psi x) := by
  dsimp only
  induction ts with
  | nil =>
    simp [realWeakJetProductSum]
    exact MemLp.zero
  | cons t ts ih =>
    have hp := real_interior_weak_product hQ (U t.2) (U (i::t.2)) (partialJet A t.1)
      (hU t (by simp)) (hD t (by simp)) (partialJet_smooth A hA t.1) i (hweak t (by simp))
    have ht := ih (fun s hs ↦ hU s (List.mem_cons_of_mem _ hs))
      (fun s hs ↦ hD s (List.mem_cons_of_mem _ hs))
      (fun s hs ↦ hweak s (List.mem_cons_of_mem _ hs))
    have hadd := real_interior_weak_add hQ _ _ _ _ hp.1 ht.1 hp.2.1 ht.2.1 i
      (fun psi hp0 hc hs ↦ (hp.2.2 psi hp0 hc hs).2.2)
      (fun psi hp0 hc hs ↦ (ht.2.2 psi hp0 hc hs).2.2)
    have hfun : (fun x ↦ partialJet A t.1 x*U (i::t.2) x+
        coordPartial (partialJet A t.1) x i*U t.2 x+
        realWeakJetProductSum A U (ts.map (fun s ↦ (i::s.1,s.2))++ts.map (fun s ↦ (s.1,i::s.2))) x) =
        realWeakJetProductSum A U ((t::ts).map (fun s ↦ (i::s.1,s.2))++(t::ts).map (fun s ↦ (s.1,i::s.2))) := by
      funext x
      simp only [realWeakJetProductSum,List.map_append,List.map_cons,List.sum_cons,List.sum_append,partialJet,coordPartial]
      ring
    rw [hfun] at hadd
    simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun hfun x] at hadd
    exact hadd

end
end Yau

end OAI
