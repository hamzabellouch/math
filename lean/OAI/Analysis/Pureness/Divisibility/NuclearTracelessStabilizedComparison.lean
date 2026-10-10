import OAI.Analysis.Pureness.Divisibility.NuclearTracelessFiniteComparison
import OAI.Analysis.Pureness.Completion.CompletedUniformComparison
import OAI.Analysis.Pureness.Completion.SharedMatrixBridge

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter Topology
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)
variable (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
  (k+1) • u ≤ k • v → u ≤ v)
variable (htrace : ¬ Nonempty (TracialState A))
include hsimple hA hAU htrace

theorem completedComparison_of_nuclear_no_trace
    (a b : CornerCompletion A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb0 : b ≠ 0) :
    CuntzSubequiv a b := by
  obtain ⟨K, hK⟩ := completedCompression_eventually_ne_zero b hb0
  have hcompare (j : ℕ) : CuntzSubequiv (completedCornerCut A (K+j+1) a) b := by
    have hbj : completedCompress A (K+j+1) b ≠ 0 := by
      intro hz
      apply hK (K+j) (Nat.le_add_right K j)
      rw [← include_completedCompress, hz, map_zero]
    have hfinite := finiteComparison_of_nuclear_no_trace hsimple hA hAU htrace (K+j+1)
      ⟨completedCompress A (K+j+1) a, completedCompress_nonneg _ a ha⟩
      ⟨completedCompress A (K+j+1) b, completedCompress_nonneg _ b hb⟩ hbj
    have hi := (cuntzSubequiv_completedMatrixInclude_iff A (K+j+1) _ _).mpr hfinite
    rw [include_completedCompress, include_completedCompress] at hi
    exact hi.trans (completedCornerCut_cuntz A (K+j+1) b)
  apply cuntzSubequiv_of_tendsto hcompare
  exact (completedCornerCut_tendsto A a).comp (tendsto_atTop.mpr (by
    intro m
    exact eventually_atTop.mpr ⟨m, fun j hj => hj.trans (by omega)⟩))

theorem stabilizedComparison_of_nuclear_no_trace
    (a b : Positive (MatrixLimit A)) (hb0 : b.1 ≠ 0) : CuntzSubequiv a.1 b.1 := by
  let e := sharedMatrixEquiv (A := A)
  have hb' : e b.1 ≠ 0 := fun h => hb0 (e.injective (h.trans e.map_zero.symm))
  have hc := completedComparison_of_nuclear_no_trace hsimple hA hAU htrace
    (e a.1) (e b.1) (map_nonneg e a.2) (map_nonneg e b.2) hb'
  obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence _ _).mp hc
  apply (cuntzSubequiv_iff_sequence _ _).mpr
  refine ⟨fun j => e.symm (v j), ?_⟩
  have hecont : Continuous e.symm :=
    (NonUnitalStarAlgHom.isometry (A := CornerCompletion A) (B := MatrixLimit A)
      e.symm.toNonUnitalStarAlgHom e.symm.injective).continuous
  have ht := hecont.continuousAt.tendsto.comp hv
  simpa only [Function.comp_def, map_mul, map_star, e.symm_apply_apply] using ht
end CuntzPureness

end

end OAI
