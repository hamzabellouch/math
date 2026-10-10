import OAI.Geometry.NodalSets.Coefficients.RealFintypeCoefficientBound
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetProducts

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis
open scoped ContDiff
noncomputable section

theorem real_weak_jet_product_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (ts : List (List (Fin 4) × List (Fin 4))) :
    ∃ C > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ t ∈ ts, MemLp (U t.2) 2 (volume.restrict Q)) →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ ts, (∫ x in Q, (U t.2 x)^2) ≤ E) →
      MemLp (realWeakJetProductSum A U ts) 2 (volume.restrict Q) ∧
      (∫ x in Q, (realWeakJetProductSum A U ts x)^2) ≤ C*E := by
  obtain ⟨C,hC,hb⟩ := real_compact_fintype_coefficient_common_bound hQ
    (fun x (a : Fin ts.length) ↦ partialJet A (ts.get a).1 x)
    (fun a ↦ (partialJet_smooth A hA (ts.get a).1).continuous)
  refine ⟨C,hC,fun U hU E hE hUE ↦ ?_⟩
  have h := hb (fun a ↦ U (ts.get a).2) (fun a ↦ hU _ (List.get_mem ..))
    E hE (fun a ↦ hUE _ (List.get_mem ..))
  have heq : (fun x ↦ ∑ a : Fin ts.length, partialJet A (ts.get a).1 x*U (ts.get a).2 x) =
      realWeakJetProductSum A U ts := by
    funext x
    dsimp [realWeakJetProductSum]
    rw [← List.sum_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map ts (fun t ↦ partialJet A t.1 x*U t.2 x)
  rw [heq] at h
  simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun heq x] at h
  exact h

end
end Yau

end OAI
