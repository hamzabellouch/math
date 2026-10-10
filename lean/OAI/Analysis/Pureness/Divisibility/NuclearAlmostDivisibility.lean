import OAI.Analysis.Pureness.Divisibility.NuclearStabilizedComparison
import OAI.Analysis.Pureness.Divisibility.NuclearTracelessAlmostDivisibility
import OAI.Analysis.Pureness.Divisibility.SharedSandwichGaps

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter Topology
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

theorem almostDivisible_of_nuclear_with_trace (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hA : IsNuclear.{u,0} A)
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (hT : Nonempty (TracialState A)) (x : CuntzClass (MatrixLimit A))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : CuntzClass (MatrixLimit A), n • y ≤ x ∧ x ≤ (n+1) • y := by
  by_cases hx : x=0
  · exact ⟨0,by simp [hx],by simp [hx]⟩
  obtain ⟨a,rfl⟩ := completedSharedClass_surjective x
  have ha0 : a.1 ≠ 0 := by
    intro hz
    apply hx
    have he : a=Positive.zero := Subtype.ext hz
    rw [he]
    change CuntzClass.mk (Positive.map sharedMatrixEquiv.symm.toNonUnitalStarAlgHom Positive.zero)=0
    have hm : Positive.map (sharedMatrixEquiv (A := A)).symm.toNonUnitalStarAlgHom Positive.zero =
        Positive.zero := Subtype.ext (map_zero _)
    rw [hm,CuntzClass.zero_mk]
  obtain ⟨b,c,d,hb0,hd0,hc,hd,hgap⟩ :=
    exists_shared_sandwich_compression_gaps hsimple hinf hT a ha0 n hn
  have hs : Tendsto (fun k : ℕ => k+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro m
    exact eventually_atTop.mpr ⟨m,fun k hk => hk.trans (Nat.le_succ k)⟩
  have hca : CuntzSubequiv c.1 a.1 :=
    cuntzSubequiv_of_tendsto (fun k =>
      completedComparison_of_nuclear_tracialRanks hsimple hA hAU
        (completedCornerCut A (k+1) c.1) a.1
        (completedCornerCut_nonneg A (k+1) c.1 c.2) a.2 ha0
        (fun τ => (hgap τ k).1)) ((completedCornerCut_tendsto A c.1).comp hs)
  have had : CuntzSubequiv a.1 d.1 :=
    cuntzSubequiv_of_tendsto (fun k =>
      completedComparison_of_nuclear_tracialRanks hsimple hA hAU
        (completedCornerCut A (k+1) a.1) d.1
        (completedCornerCut_nonneg A (k+1) a.1 a.2) d.2 hd0
        (fun τ => (hgap τ k).2)) ((completedCornerCut_tendsto A a.1).comp hs)
  refine ⟨completedSharedClass b, ?_, ?_⟩
  · rw [← hc]
    exact (completedSharedClass_le_iff c a).mpr hca
  · rw [← hd]
    exact (completedSharedClass_le_iff a d).mpr had

theorem almostDivisible_of_simple_infinite_nuclear (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hA : IsNuclear.{u,0} A)
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (x : CuntzClass (MatrixLimit A)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : CuntzClass (MatrixLimit A), n • y ≤ x ∧ x ≤ (n+1) • y := by
  by_cases hT : Nonempty (TracialState A)
  · exact almostDivisible_of_nuclear_with_trace hsimple hinf hA hAU hT x n hn
  · exact almostDivisible_of_nuclear_no_trace hsimple hA hAU hT x n
end CuntzPureness

end

end OAI
