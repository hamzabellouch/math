import OAI.Probability.MatroidSecretary.Density.DensityContractsModel
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Proofs of the complete source-facing density, paths and generator contracts. -/
namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

/-- Closing the lower constraint leaves exactly the same feasible flat family. -/
lemma densityExpansion_closure_argument (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) :
    densityExpansion M hE κ D (M.closure P) = densityExpansion M hE κ D P := by
  apply Subset.antisymm
  · apply (densityExpansion_spec M hE κ D P).2
    obtain ⟨hQflat, hPQ, hmax⟩ := (densityExpansion_spec M hE κ D (M.closure P)).1
    refine ⟨hQflat, (M.subset_closure P (by simp [hE])).trans hPQ, ?_⟩
    intro Z hZ hPZ
    apply hmax Z hZ
    exact (M.closure_subset_closure hPZ).trans_eq hZ.closure
  · exact densityExpansion_mono M hE κ D (M.subset_closure P (by simp [hE]))

lemma densityExpansion_residual_conditionalRank (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P Z : Set α) :
    (D ∩ (M.closure (densityExpansion M hE κ D P ∪ Z) \
      densityExpansion M hE κ D P)).ncard ≤
      κ * conditionalRank M Z (densityExpansion M hE κ D P) := by
  have hb := densityExpansion_residual M hE κ D P Z
  dsimp only at hb
  have hr := conditionalRank_add_base M Z (densityExpansion M hE κ D P)
  rw [union_comm Z] at hr
  have hm := congrArg (fun x : ℕ => κ * x) hr
  rw [Nat.mul_add] at hm
  omega

/-- Full `lem:density`, without assuming existence or correctness of its expansion. -/
theorem source_density_expansion (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) : DensityExpansionContract M hE κ D := by
  refine ⟨fun _ _ h => densityExpansion_mono M hE κ D h, ?_⟩
  intro P
  exact ⟨(densityExpansion_spec M hE κ D P).1,
    (densityExpansion_spec M hE κ D P).2,
    densityExpansion_extensive M hE κ D P,
    densityExpansion_closure_argument M hE κ D P,
    densityExpansion_residual_conditionalRank M hE κ D P⟩

/-- Full `lem:paths`; the birth is certified least on the complete integer timeline. -/
theorem source_path_properties (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) : PathPropertiesContract M hE κ D C := by
  intro h
  refine ⟨nominalPath_mono M hE κ D C h, guardedPath_mono M hE κ D C (h + 1),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨guarded_subset_nominal M hE κ D C h k,
      nominal_subset_guarded M hE κ D C h k,
      guarded_subset_next_nominal M hE κ D C h k⟩
  · intro k hk
    exact ⟨nominalPath_nonnegative M hE κ D C h hk,
      guardedPath_nonnegative M hE κ D C (h + 1) hk⟩
  · exact fun k hk => nominalPath_early M hE κ D C h hk
  · intro k hk
    apply guardedPath_early
    dsimp [activation] at hk
    push_cast
    omega
  · intro e he
    refine ⟨⟨nominalBirth_mem M hE κ D C h e, ?_⟩, ?_⟩
    · intro k hk
      exact (mem_nominal_iff_birth_le M hE κ D C h e he k).mp hk
    · rcases nominalBirth_range M hE κ D C h e with hb | hb
      · exact Or.inl ⟨hb, (baseline_birth_iff M hE κ D C h e he).mp hb⟩
      · exact Or.inr hb

/-- Full `lem:generators`, including monotonicity outside the bounded computation. -/
theorem source_generator_budget (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) :
    GeneratorBudgetContract M hE κ D C := by
  intro h
  refine ⟨?_, baseline_density_rank M hE κ (D h)⟩
  obtain ⟨G, hGD, hcard, τ, _, hgen⟩ := nominalPath_all_time_generators M hE κ hκ D C h
  refine ⟨G, hGD, hcard, timedGeneratorSet G τ (activation h), ?_, ?_, hgen⟩
  · intro i j hij e he
    exact ⟨he.1, he.2.trans hij⟩
  · exact fun _ _ he => he.1

end MatroidProphet

end OAI
