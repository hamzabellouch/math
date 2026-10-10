import OAI.Analysis.Pureness.Divisibility.NuclearCompletedFiniteComparison
import OAI.Analysis.Pureness.Completion.CompletedFiniteEnvelope

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter Topology
open scoped NNReal ENNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)
variable (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
  (k+1) • u ≤ k • v → u ≤ v)
include hsimple hA hAU

theorem completedComparison_of_nuclear_tracialRanks
    (a b : CornerCompletion A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb0 : b ≠ 0)
    (hgap : ∀ τ : TracialState A, completedRootRank τ a < completedRootRank τ b) :
    CuntzSubequiv a b := by
  have hfinite (k : ℕ) : CuntzSubequiv (completedCornerCut A k a) b := by
    let M : Positive (FinMatrix A k) :=
      ⟨completedCompress A k a, completedCompress_nonneg k a ha⟩
    have hcut (δ : ℝ≥0) (hδ : 0 < δ) :
        CuntzSubequiv (completedMatrixInclude A k (Positive.cut δ M).1) b := by
      obtain ⟨F,hF,hbounds⟩ := exists_completedFinite_trace_envelope k M δ hδ
      obtain ⟨l,hl0,hlgap⟩ := exists_nonzero_completedCompression_rank_gap b hb hb0 F hF
        (fun τ => by
          apply (hbounds τ).2.trans_lt
          change completedRootRank τ (completedMatrixInclude A k (completedCompress A k a)) < _
          rw [include_completedCompress]
          exact (completedRootRank_cut_le τ k a ha).trans_lt (hgap τ))
      let N : Positive (FinMatrix A (l+1)) :=
        ⟨completedCompress A (l+1) b, completedCompress_nonneg (l+1) b hb⟩
      have hN : N.1 ≠ 0 := by
        intro hz
        apply hl0
        rw [← include_completedCompress]
        change completedMatrixInclude A (l+1) N.1=0
        rw [hz,map_zero]
      have hc := nuclear_completedFiniteComparison hsimple hA hAU k (l+1)
        (Positive.cut δ M) N hN (fun τ => by
          have h := (hbounds τ).1.trans_lt (hlgap τ)
          simpa only [N,include_completedCompress] using h)
      change CuntzSubequiv (completedMatrixInclude A k (Positive.cut δ M).1)
        (completedMatrixInclude A (l+1) (completedCompress A (l+1) b)) at hc
      rw [include_completedCompress] at hc
      exact hc.trans (completedCornerCut_cuntz A (l+1) b)
    let δ : ℕ → ℝ≥0 := fun j => 1 / ((j : ℝ≥0)+1)
    have hδ : Tendsto (fun j => (δ j : ℝ)) atTop (𝓝 0) := by
      simpa [δ] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun j : ℕ => 1 / ((j : ℝ)+1)) atTop (𝓝 0))
    have ht := (completedMatrixInclude_isometry A k).continuous.continuousAt.tendsto.comp
      ((continuous_subtype_val.tendsto M).comp (Positive.tendsto_cut δ hδ M))
    have hc := cuntzSubequiv_of_tendsto (fun j => hcut (δ j) (by dsimp [δ]; positivity)) ht
    simpa only [M,include_completedCompress] using hc
  exact cuntzSubequiv_of_tendsto hfinite (completedCornerCut_tendsto A a)

theorem stabilizedComparison_of_nuclear_tracialRanks
    (a b : Positive (MatrixLimit A)) (hb0 : b.1 ≠ 0)
    (hgap : ∀ τ : TracialState A, (sharedExtendedTrace τ).rank a <
      (sharedExtendedTrace τ).rank b) : CuntzSubequiv a.1 b.1 := by
  let e := sharedMatrixEquiv (A := A)
  have hb' : e b.1 ≠ 0 := fun h => hb0 (e.injective (h.trans e.map_zero.symm))
  have hc := completedComparison_of_nuclear_tracialRanks hsimple hA hAU
    (e a.1) (e b.1) (map_nonneg e a.2) (map_nonneg e b.2) hb'
    (fun τ => by simpa only [sharedExtendedTrace_rank] using hgap τ)
  obtain ⟨v,hv⟩ := (cuntzSubequiv_iff_sequence _ _).mp hc
  apply (cuntzSubequiv_iff_sequence _ _).mpr
  refine ⟨fun j => e.symm (v j), ?_⟩
  have hecont : Continuous e.symm :=
    (NonUnitalStarAlgHom.isometry (A := CornerCompletion A) (B := MatrixLimit A)
      e.symm.toNonUnitalStarAlgHom e.symm.injective).continuous
  have ht := hecont.continuousAt.tendsto.comp hv
  simpa only [Function.comp_def,map_mul,map_star,e.symm_apply_apply] using ht
end CuntzPureness

end

end OAI
