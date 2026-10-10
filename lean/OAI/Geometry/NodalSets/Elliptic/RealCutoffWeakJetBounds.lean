import OAI.Geometry.NodalSets.Elliptic.RealCutoffWeakJets
import OAI.Geometry.NodalSets.Elliptic.RealFiniteWordBounds
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetProductBound

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

theorem real_cutoff_weak_jet_square_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (eta : Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ Q) (N : ℕ) :
    ∃ C > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ es, es.length ≤ N → MemLp (U es) 2 (volume.restrict Q)) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N → (∫ x in Q, (U es x)^2) ≤ E) →
      ∀ ds, ds.length ≤ N →
        (∫ x, (realWeakJetExpansion eta U [] ds x)^2) ≤ C*E := by
  have hex (ds : List (Fin 4)) :=
    real_weak_jet_product_bound hQ eta he (([],ds)::realJetErrorTerms [] ds)
  choose C hC hb using hex
  obtain ⟨B,hB,hmajor⟩ := real_finite_word_positive_majorant 4 N C
  refine ⟨B,hB,fun U hU E hE hUE ds hd ↦ ?_⟩
  have hord (t : List (Fin 4) × List (Fin 4))
      (ht : t ∈ ([],ds)::realJetErrorTerms [] ds) : t.2.length ≤ N := by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hd
    · exact ((realJetErrorTerms_orders [] ds (by simp) t ht).2).trans hd
  have h := hb ds U (fun t ht ↦ hU _ (hord t ht)) E hE (fun t ht ↦ hUE _ (hord t ht))
  have hid : realWeakJetProductSum eta U (([],ds)::realJetErrorTerms [] ds)=
      realWeakJetExpansion eta U [] ds := by
    funext x
    simp only [realWeakJetProductSum,List.map_cons,List.sum_cons,partialJet,
      realWeakJetExpansion,List.nil_append]
  rw [hid] at h
  have hz : ∀ x, x ∉ Q → (realWeakJetExpansion eta U [] ds x)^2=0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx
      (hs (realWeakJetExpansion_support eta U [] ds hh))),zero_pow (by decide)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact h.2.trans (mul_le_mul_of_nonneg_right (hmajor ds hd) hE)

end
end Yau

end OAI
