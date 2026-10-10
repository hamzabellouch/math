import OAI.Probability.MatroidProphet.Density.Birth
import OAI.Probability.MatroidProphet.LayerRank

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

omit [Fintype α] in
lemma natRank_eq_ncard_of_indep (M : Matroid α) {I : Set α} (hI : M.Indep I) :
    natRank M I = I.ncard := by
  simp only [natRank, hI.eRk_eq_encard, Set.ncard_def]

lemma baseline_density_rank (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ) (D : Set α) :
    κ * natRank M (densityExpansion M hE κ D (M.closure ∅)) ≤ D.ncard := by
  let Q := densityExpansion M hE κ D (M.closure ∅)
  have hmax := (densityExpansion_spec M hE κ D (M.closure ∅)).1.2.2
    (M.closure ∅) (Matroid.isFlat_closure (M := M) ∅) Set.Subset.rfl
  have hcount := Set.ncard_mono (show D ∩ Q ⊆ D from inter_subset_left)
  have hnn : (0 : ℤ) ≤ (D ∩ M.closure ∅).ncard := by exact_mod_cast Nat.zero_le _
  have hcount' : ((D ∩ Q).ncard : ℤ) ≤ D.ncard := by exact_mod_cast hcount
  have hmax' : (κ : ℤ) * natRank M Q ≤ D.ncard := by
    dsimp only [densityObjective] at hmax
    rw [natRank_closure, natRank_empty] at hmax
    change _ ≤ (D ∩ Q).ncard - (κ : ℤ) * natRank M Q at hmax
    omega
  exact_mod_cast hmax'

lemma baseline_independent_count (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D I : Set α) (hI : M.Indep I) :
    κ * (I ∩ densityExpansion M hE κ D (M.closure ∅)).ncard ≤ D.ncard := by
  have hi := natRank_eq_ncard_of_indep M
    (hI.subset (show I ∩ densityExpansion M hE κ D (M.closure ∅) ⊆ I from inter_subset_left))
  have hr := natRank_mono M (show I ∩ densityExpansion M hE κ D (M.closure ∅) ⊆
      densityExpansion M hE κ D (M.closure ∅) from inter_subset_right)
  rw [hi] at hr
  exact (Nat.mul_le_mul_left κ hr).trans (baseline_density_rank M hE κ D)

lemma baseline_birth_iff (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) :
    nominalBirth M hE κ D C h d = activation h ↔
      d ∈ densityExpansion M hE κ (D h) (M.closure ∅) := by
  rw [← nominalPath_baseline M hE κ D C h,
    mem_nominal_iff_birth_le M hE κ D C h d hd]
  exact ⟨fun he => he.le, fun he => le_antisymm he (nominalBirth_bounds M hE κ D C h d).1⟩

end MatroidProphet

end OAI
