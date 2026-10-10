import OAI.Geometry.NodalSets.Elliptic.RealSupportedWeakGlobal
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetLeibniz

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

lemma realWeakJetProductSum_support (A : Jets.Coord → ℝ)
    (U : List (Fin 4) → Jets.Coord → ℝ) (ts : List (List (Fin 4) × List (Fin 4))) :
    tsupport (realWeakJetProductSum A U ts) ⊆ tsupport A := by
  induction ts with
  | nil =>
    change tsupport (fun _ : Jets.Coord ↦ (0:ℝ)) ⊆ tsupport A
    simp
  | cons t ts ih =>
    exact (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_left.trans (partialJet_tsupport_subset A t.1)) ih)

lemma realWeakJetExpansion_support (A : Jets.Coord → ℝ)
    (U : List (Fin 4) → Jets.Coord → ℝ) (extra ds : List (Fin 4)) :
    tsupport (realWeakJetExpansion A U extra ds) ⊆ tsupport A :=
  (tsupport_add _ _).trans (union_subset tsupport_mul_subset_left (realWeakJetProductSum_support A U _))

theorem real_cutoff_finite_weak_jet {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (eta : Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior Q) (U : List (Fin 4) → Jets.Coord → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q))
    (hw : ∀ es, es.length ≤ N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) :
    let V := realWeakJetExpansion eta U []
    (∀ ds, ds.length ≤ N → MemLp (V ds) 2 volume ∧ tsupport (V ds) ⊆ tsupport eta) ∧
    ∀ ds, ds.length < N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi →
      Integrable (fun x ↦ V ds x*coordPartial psi x i) ∧ Integrable (fun x ↦ V (i::ds) x*psi x) ∧
      (∫ x, V ds x*coordPartial psi x i)=-(∫ x, V (i::ds) x*psi x) := by
  have hv (ds : List (Fin 4)) (hd : ds.length ≤ N) :
      MemLp (realWeakJetExpansion eta U [] ds) 2 volume := by
    have hl := real_weak_jet_expansion_memLp hQ eta he U N hU [] ds (by simp) hd
    have hg := (memLp_indicator_iff_restrict hQ.measurableSet).mpr hl
    have hid : Q.indicator (realWeakJetExpansion eta U [] ds)=realWeakJetExpansion eta U [] ds := by
      apply indicator_eq_self.mpr
      exact subset_tsupport _ |>.trans ((realWeakJetExpansion_support eta U [] ds).trans (hs.trans interior_subset))
    rwa [hid] at hg
  refine ⟨fun ds hd ↦ ⟨hv ds hd,realWeakJetExpansion_support eta U [] ds⟩,?_⟩
  intro ds hd i
  have hl := real_weak_jet_expansion_derivative hQ eta he U N hU hw [] ds (by simp) hd i
  exact (real_supported_local_weak_global hQ hc hs _ _ hl.1 hl.2.1
    (realWeakJetExpansion_support eta U [] ds) (realWeakJetExpansion_support eta U [] (i::ds)) i
    (fun psi hp hc hs ↦ (hl.2.2 psi hp hc hs).2.2)).2.2

end
end Yau

end OAI
