import OAI.Combinatorics.BalancedRyser.Local.AlignedCoordinateAveraging
import OAI.Combinatorics.BalancedRyser.Local.AlignedPointLaw
import OAI.Combinatorics.BalancedRyser.Local.LocalBadCoverSpecifications
import OAI.Combinatorics.BalancedRyser.Local.LocalSpecificationTransport
import OAI.Combinatorics.BalancedRyser.Probability.FiniteDependencyRank

namespace OAI

namespace Balanced.Local.AlignedGlobal

noncomputable section
open scoped Classical
open RootChildPartition AlignedUnused ConditionSpec

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem PointSystem.fixedUnused_badCover_bound
    {P : EqualityPattern b κ} {a : DirectionAssignment F b κ}
    {bits : Bits b} {p : Point F} {R : Finset (Fin b)}
    (S : PointSystem P a bits p R) (hκ : κ ≤ 2)
    (hD : (dependentOccurrences P R).card = 2 * κ) (ha : Eligible P a)
    (hb : 1 ≤ b) (hB : 1 ≤ logBudget F)
    (hextract : ∀ M, AdmissibleBadCover P a bits p M →
      ∃ σ : Fin (3 - κ) → Position b × Code b κ,
        GoodSpecification S.underlying (Finset.univ \ dependentOccurrences P R) σ ∧
          ∀ k, Holds P a bits p M (σ k).1 (σ k).2)
    (z : UnusedArray P a) :
    UnusedOffsetIncidence.probability (fun x : FreeIndex P R → F =>
      AdmissibleBadCover P a bits p
        ((coordinateEquiv P hκ R hD a ha bits p).symm (x,z)).1) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ) := by
  let e := coordinateEquiv P hκ R hD a ha bits p
  let Ms : (FreeIndex P R → F) → MergedPairs F := fun x => (e.symm (x,z)).1
  apply admissibleBadCover_fixedUnused_bound P a bits p (Ms (fun _ => 0)) Ms
    S.underlying S.point (Finset.univ \ dependentOccurrences P R) hb hB
  · intro x d hd
    have hdu : d ∉ usedDirections P a := by
      simpa only [ConditionSpec.unusedDirections, Finset.mem_sdiff,
        Finset.mem_univ, true_and, FourEvents.usedDirections, usedDirections] using hd
    exact (generated_unused P hκ R hD a ha bits p (x,z) ⟨d,hdu⟩).trans
      (generated_unused P hκ R hD a ha bits p ((fun _ => 0),z) ⟨d,hdu⟩).symm
  · intro x v
    exact S.generated_points hκ hD ha (x,z) v
  · intro v hv
    exact S.free_injective ⟨v, (Finset.mem_sdiff.mp hv).2⟩
  · intro v hv t
    exact S.free_onLine ⟨v, (Finset.mem_sdiff.mp hv).2⟩ t
  · intro x hx
    exact hextract (Ms x) hx

theorem PointSystem.badCover_probability_bound
    {P : EqualityPattern b κ} {a : DirectionAssignment F b κ}
    {bits : Bits b} {p : Point F} {R : Finset (Fin b)}
    (S : PointSystem P a bits p R) (hκ : κ ≤ 2)
    (hD : (dependentOccurrences P R).card = 2 * κ) (ha : Eligible P a)
    (hb : 1 ≤ b) (hB : 1 ≤ logBudget F)
    (hextract : ∀ M, AdmissibleBadCover P a bits p M →
      ∃ σ : Fin (3 - κ) → Position b × Code b κ,
        GoodSpecification S.underlying (Finset.univ \ dependentOccurrences P R) σ ∧
          ∀ k, Holds P a bits p M (σ k).1 (σ k).2) :
    conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ) := by
  apply conditionedOffsetProbability_le_of_freeCoordinate_fibers P hκ R hD a ha bits p
  intro z
  rw [← UnusedOffsetIncidence.probability_eq_pmf]
  exact S.fixedUnused_badCover_bound hκ hD ha hb hB hextract z

theorem goodSpecification_lift {α β : Type*} [DecidableEq α] [DecidableEq β]
    {n : ℕ} {u : Position b → α} (v : Position b → β) (f : β → α)
    (hfv : ∀ w, f (v w) = u w) {I : Finset (Position b)}
    {σ : Fin n → Position b × Code b κ} (h : GoodSpecification u I σ) :
    GoodSpecification v I σ := by
  obtain ⟨hinj, hI, rank, hrank⟩ := h
  refine ⟨?_, hI, rank ∘ f, ?_⟩
  · intro i j hij
    apply hinj
    exact (hfv _).symm.trans ((congrArg f hij).trans (hfv _))
  · intro i j hij
    simp only [Function.comp_apply, hfv]
    apply hrank i j
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hij
    exact Finset.mem_image.mpr ⟨w, hw,
      (hfv w).symm.trans ((congrArg f heq).trans (hfv _))⟩

theorem smallReuse_badCover_probability_bound
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (hb : 3 ≤ b) (hB : b ≤ logBudget F)
    (hκ : κ ≤ 1) (ha : Eligible P a) :
    conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hκ with rfl | rfl
  · let R : Finset (Fin b) := Finset.univ
    have hdep : dependentOccurrences P R = ∅ := by simp [R, dependentOccurrences]
    have hD : (dependentOccurrences P R).card = 2 * 0 := by simp [hdep]
    let S := pointSystemOfNoDependents P a bits p R hdep
    apply S.badCover_probability_bound (by omega) hD ha (by omega) (by omega)
    intro M hM
    obtain ⟨σ, hσ, hholds⟩ := badCover_zero_reuse_exists_goodSpecification
      P a bits p M hb ha hM.1 hM.2
    refine ⟨σ, ?_, hholds⟩
    have hg : GoodSpecification id (Finset.univ \ dependentOccurrences P R) σ := by
      simpa only [hdep, Finset.sdiff_empty] using hσ
    exact goodSpecification_lift S.underlying Subtype.val (fun _ => rfl) hg
  · obtain ⟨R, root, child, r, s, _, _, _, hne, _, _, hshared, hdep, _⟩ :=
      exists_one_reuse_linked_pair P hb
    have hdep' : dependentOccurrences P R = ParentMap.dependent child s := hdep
    have hD : (dependentOccurrences P R).card = 2 * 1 := by
      rw [hdep']
      have hne' : (child,s) ≠ (child,s-1) := by
        intro h
        exact ParentMap.sub_one_ne s (congrArg Prod.snd h).symm
      simp [ParentMap.dependent, hne']
    let S := pointSystemOfLinkedPair P a ha bits p R root child r s hne hshared hdep'
    apply S.badCover_probability_bound (by omega) hD ha (by omega) (by omega)
    intro M hM
    obtain ⟨σ, hσ, hholds⟩ := badCover_one_reuse_exists_goodSpecification
      P a bits p M hb ha hM.1 hM.2 root child r s hshared
    refine ⟨σ, ?_, hholds⟩
    have hg : GoodSpecification
        (ParentMap.underlying root child r s (bits root r) (bits child s))
        (Finset.univ \ dependentOccurrences P R) σ := by
      simpa only [hdep'] using hσ
    exact goodSpecification_lift S.underlying Subtype.val (fun _ => rfl) hg

end
end Balanced.Local.AlignedGlobal

namespace Balanced.Local

universe u

theorem pencilSmallReuse_proof : PencilSmallReuseResult.{u} := by
  refine ⟨alignmentNormalization_proof, (148 : ℝ) ^ 3, by positivity, 9, 0, ?_⟩
  intro F _ _ _ _ b κ hb hB hκ P a ha bits p
  exact AlignedGlobal.smallReuse_badCover_probability_bound P a bits p hb hB hκ ha

end Balanced.Local

end OAI
