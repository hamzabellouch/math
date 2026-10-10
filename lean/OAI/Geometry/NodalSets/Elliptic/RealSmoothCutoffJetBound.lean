import OAI.Geometry.NodalSets.Elliptic.RealCutoffWeakJetBounds
import OAI.Geometry.NodalSets.Elliptic.RealGlobalJetCommonBound
import OAI.Geometry.NodalSets.Elliptic.RealSmoothWeakJetIdentification

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

theorem real_smooth_cutoff_jet_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (eta : Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior Q) (n : ℕ) :
    ∃ C > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ es, es.length ≤ n+5 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ n+4 → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ n+4 → (∫ x in Q, (U es x)^2) ≤ E) →
      ∀ v : Jets.Coord → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
        v =ᵐ[volume] (fun x ↦ eta x*U [] x) →
        ∀ ds, ds.length ≤ n → ∀ x, (partialJet v ds x)^2 ≤ C*E := by
  obtain ⟨A,hA,ha⟩ := real_cutoff_weak_jet_square_bound hQ eta he (hs.trans interior_subset) (n+4)
  obtain ⟨B,hB,hb⟩ := real_global_jet_common_bound n
  refine ⟨B*A,mul_pos hB hA,fun U hU hw E hE hUE v hv hvc hve ds hd x ↦ ?_⟩
  let V := realWeakJetExpansion eta U []
  have hV := real_cutoff_finite_weak_jet hQ eta he hc hs U (n+4) hU hw
  have hz : v =ᵐ[volume] V [] := by
    change v =ᵐ[volume] (fun x ↦ realWeakJetExpansion eta U [] [] x)
    simpa only [V,realWeakJetExpansion,realJetErrorTerms,realWeakJetProductSum,
      List.append_nil,List.map_nil,List.sum_nil,add_zero] using hve
  have heq (es : List (Fin 4)) (hh : es.length ≤ n+4) : partialJet v es =ᵐ[volume] V es :=
    real_smooth_weak_jet_ae V (n+4)
      (fun es hh ↦ ⟨(hV.1 es hh).1,hc.of_isClosed_subset (isClosed_tsupport _) (hV.1 es hh).2⟩)
      (fun es hh i psi hp hc ↦ (hV.2 es hh i psi hp hc).2.2) v hv hz es hh
  have hbound (es : List (Fin 4)) (hh : es.length ≤ n+4) :
      (∫ x, (partialJet v es x)^2) ≤ A*E := by
    have hid := integral_congr_ae ((heq es hh).fun_comp (fun t : ℝ ↦ t^2))
    dsimp only [Function.comp_def] at hid
    rw [hid]
    exact ha U (fun es hh ↦ hU es (by omega)) E hE hUE es hh
  simpa only [mul_assoc] using hb v hv hvc (A*E) (mul_nonneg hA.le hE) hbound ds hd x

end
end Yau

end OAI
