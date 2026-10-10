import OAI.Analysis.BoundedHochschild.RepresentedAveragingConvexity

namespace OAI

/-! Minimal families for represented right averages, and constancy of
commutant-compressed norms. This is the first step of the minimal-family
argument in Paulsen, J. Funct. Anal. 157 (1998), Theorem 5.8, pp. 378–379. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def RepresentedRightAverageInvariant (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Set (H →WOT[ℂ] K)) : Prop :=
  ∀ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) →
    Set.MapsTo (weakRepresentedRightAverage π σ m) F F

theorem exists_minimal_represented_averages (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    ∃ F : Set (H →WOT[ℂ] K), F ⊆ closedRepresentedAveragingOrbit π σ W ∧
      F.Nonempty ∧ IsClosed F ∧ Convex ℝ F ∧ RepresentedRightAverageInvariant π σ F ∧
      ∀ G : Set (H →WOT[ℂ] K), G ⊆ F → G.Nonempty → IsClosed G →
        Convex ℝ G → RepresentedRightAverageInvariant π σ G → F ⊆ G := by
  classical
  let B := closedRepresentedAveragingOrbit π σ W
  have hBc : IsCompact B := closedRepresentedAveragingOrbit_isCompact π σ W
  let S : Set (Set (H →WOT[ℂ] K)) := {F | F ⊆ B ∧ F.Nonempty ∧ IsClosed F ∧
    Convex ℝ F ∧ RepresentedRightAverageInvariant π σ F}
  have hBS : B ∈ S := ⟨Set.Subset.rfl,
    ⟨W, subset_closure (representedAveragingOrbit_self π σ W)⟩,
    isClosed_closure, closedRepresentedAveragingOrbit_convex π σ W,
    fun _ m hm => closedRepresentedAveragingOrbit_invariant π σ m hm W⟩
  obtain ⟨F, hFB, hF⟩ := zorn_superset_nonempty S (fun c hc hchain hcne => by
    have : Nonempty c := hcne.to_subtype
    have hn : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun A hA B hB => by
          rcases hchain.total hA hB with h | h
          · exact ⟨A, hA, Set.Subset.rfl, h⟩
          · exact ⟨B, hB, h, Set.Subset.rfl⟩)
        (fun A hA => (hc hA).2.1)
        (fun A hA => hBc.of_isClosed_subset (hc hA).2.2.1 (hc hA).1)
        (fun A hA => (hc hA).2.2.1)
    refine ⟨⋂₀ c, ⟨?_, hn, ?_, ?_, ?_⟩, fun A hA => Set.sInter_subset_of_mem hA⟩
    · obtain ⟨A, hA⟩ := hcne
      exact (Set.sInter_subset_of_mem hA).trans (hc hA).1
    · exact isClosed_sInter (fun A hA => (hc hA).2.2.1)
    · intro x hx y hy r s hr hs hrs
      apply Set.mem_sInter.mpr
      intro A hA
      exact (hc hA).2.2.2.1 (Set.mem_sInter.mp hx A hA)
        (Set.mem_sInter.mp hy A hA) hr hs hrs
    · intro n m hm x hx
      apply Set.mem_sInter.mpr
      intro A hA
      exact (hc hA).2.2.2.2 n m hm (Set.mem_sInter.mp hx A hA)) B hBS
  exact ⟨F, hFB, hF.1.2.1, hF.1.2.2.1, hF.1.2.2.2.1, hF.1.2.2.2.2,
    fun G hGF hGn hGc hGv hGi => hF.2 ⟨hGF.trans hFB, hGn, hGc, hGv, hGi⟩ hGF⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
