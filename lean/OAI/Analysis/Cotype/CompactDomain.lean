import OAI.Analysis.Cotype.CompactMomentAssembly
import OAI.Analysis.Cotype.DualCotypeFromLifts

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (A : ℕ → Submodule ℝ X)
local instance : IsClosed ((weightedMap A).ker : Set (LevelSum A)) := (weightedMap A).isClosed_ker
local instance : NormedAddCommGroup (KernelQuotient (weightedMap A)) :=
  Submodule.Quotient.normedAddCommGroup (weightedMap A).ker

theorem exists_quotient_moment_lift {m : ℕ} {D : ℝ} (hD : 0 < D)
    (hL : ∀ l, FiniteLevelLift m D (A l) (A (l+1)))
    (g : Fin m → KernelQuotient (weightedMap A)) :
    ∃ H : Cube m → KernelQuotient (weightedMap A),
      (∀ i, moment (KernelQuotient (weightedMap A)) H i = g i) ∧
      cubeL2 (KernelQuotient (weightedMap A)) H ≤ 12*D*Real.sqrt (∑ i, ‖g i‖^2) := by
  choose z hz hzn using (fun i => quotient_representative_two (weightedMap A) (g i))
  obtain ⟨H, hHm, hHn⟩ := exists_levelSum_moment_lift A hD hL z
  let Q : LevelSum A →L[ℝ] KernelQuotient (weightedMap A) := (weightedMap A).ker.mkQL
  refine ⟨fun ε => Q (H ε), ?_, ?_⟩
  · intro i
    apply quotientFactor_injective (weightedMap A)
    rw [← moment_clm Q H i, quotientFactor_mk, ← hz i, quotientFactor_mk]
    exact hHm i
  · have hQ : cubeL2 (KernelQuotient (weightedMap A)) (fun ε => Q (H ε)) ≤ cubeL2 (LevelSum A) H :=
      cubeL2_mono (fun ε => Submodule.Quotient.norm_mk_le (weightedMap A).ker (H ε))
    have hzN : Real.sqrt (∑ i, ‖z i‖^2) ≤ 2 * Real.sqrt (∑ i, ‖g i‖^2) := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), mul_pow,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => by
        simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg (z i)) (by positivity)).mpr (hzn i))
    exact hQ.trans (hHn.trans (by nlinarith [mul_le_mul_of_nonneg_left hzN (by positivity : 0 ≤ 6*D)]))

theorem quotient_dual_fixedCotype {m : ℕ} {D : ℝ} (hD : 0 < D)
    (hL : ∀ l, FiniteLevelLift m D (A l) (A (l+1))) :
    FixedCotypeBound (KernelQuotient (weightedMap A) →L[ℝ] ℝ) m (12*D) :=
  fixedCotypeBound_dual_of_L2_lifts (X := KernelQuotient (weightedMap A))
    (by positivity) (exists_quotient_moment_lift A hD hL)

structure CompactDomainWitness (E : Submodule ℝ X) (m : ℕ) (D : ℝ) where
  G : Type u
  [normedGroup : NormedAddCommGroup G]
  [normedSpace : NormedSpace ℝ G]
  [completeSpace : CompleteSpace G]
  J : G →L[ℝ] X
  iota : E →L[ℝ] G
  injective : Function.Injective J
  compact : IsCompactOperator J
  norm_J : ‖J‖ ≤ 2
  norm_iota : ‖iota‖ ≤ 1
  factor : ∀ x, J (iota x) = (x : X)
  dual_cotype : FixedCotypeBound (G →L[ℝ] ℝ) m (12*D)

theorem exists_compactDomain {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDp : 0 < D)
    (E : Submodule ℝ X) [FiniteDimensional ℝ E] :
    Nonempty (CompactDomainWitness E m D) := by
  obtain ⟨A,hA0,hmono,hAfin,hL⟩ := exists_finiteLevel_tower hD hDp E
  let (l : ℕ) : FiniteDimensional ℝ (A l) := hAfin l
  subst E
  exact ⟨{ G := KernelQuotient (weightedMap A)
           J := quotientFactor (weightedMap A)
           iota := compactInclusion A
           injective := quotientFactor_injective _
           compact := quotientFactor_compact _ (weightedMap_compact A hAfin)
           norm_J := (quotientFactor_norm _).trans (weightedMap_norm A)
           norm_iota := compactInclusion_norm A
           factor := quotientFactor_compactInclusion A
           dual_cotype := quotient_dual_fixedCotype A hDp hL }⟩

end Cotype

end

end OAI
