import OAI.Geometry.NodalSets.Elliptic.RealAllWeakJetsSmooth
import OAI.Geometry.NodalSets.Elliptic.RealCutoffWeakJets

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

theorem real_local_weak_jets_smooth {Q L : Set Jets.Coord}
    (hQ : IsCompact Q) (hL : IsCompact L)
    (eta : Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior Q) (hLeta : tsupport eta ⊆ interior L)
    (u : Jets.Coord → ℝ)
    (hall : ∀ N : ℕ, ∃ U : List (Fin 4) → Jets.Coord → ℝ,
      U []=u ∧
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) ∧
      ∀ es, es.length ≤ N → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) :
    ∃ v : Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ tsupport v ⊆ L ∧
      v =ᵐ[volume] (fun x ↦ eta x*u x) := by
  apply real_all_weak_jets_smooth hc hL hLeta
  intro N
  obtain ⟨U,hzero,hU,hw⟩ := hall N
  have h := real_cutoff_finite_weak_jet hQ eta he hc hs U N hU hw
  refine ⟨realWeakJetExpansion eta U [],?_,h.1,?_⟩
  · funext x
    simp only [realWeakJetExpansion,realJetErrorTerms,realWeakJetProductSum,
      List.append_nil,List.map_nil,List.sum_nil,add_zero,hzero]
  · intro es hh i psi hp hc
    exact (h.2 es hh i psi hp hc).2.2

end
end Yau

end OAI
