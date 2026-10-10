import OAI.Combinatorics.BalancedRyser.Candidates.CandidateBasics
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionAssignments
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionCoordinates
import OAI.Combinatorics.BalancedRyser.Deletion.GeometricDeletionCounting
import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletion
import OAI.Combinatorics.BalancedRyser.Probability.UniformKernel

namespace OAI

open scoped BigOperators

namespace Balanced.SelectedDeletionCoordinates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev SingleOffsets (F : Type*) := Direction F → F
abbrev SplitOffsets (F : Type*) := Slot F → F

def offsetPairEquiv : (SingleOffsets F × SingleOffsets F) ≃ MergedPairs F where
  toFun M d b := if b then M.2 d else M.1 d
  invFun M := (fun d => M d false, fun d => M d true)
  left_inv M := by rfl
  right_inv M := by funext d b; cases b <;> rfl

def roles (ω : SingleOffsets F × SplitOffsets F) (d : Direction F) : Fin 3 → F :=
  ![ω.1 d, ω.2 (d, false), ω.2 (d, true)]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem roles_injective : Function.Injective (@roles F) := by
  intro a b h
  apply Prod.ext
  · funext d
    simpa [roles] using congrFun (congrFun h d) (0 : Fin 3)
  · funext s
    obtain ⟨d, t⟩ := s
    cases t
    · simpa [roles] using congrFun (congrFun h d) (1 : Fin 3)
    · simpa [roles] using congrFun (congrFun h d) (2 : Fin 3)

theorem mem_selected_deletedLines (M : MergedPairs F) (f : SplitOffsets F)
    (d : Direction F) (a : F) :
    (d, a) ∈ (selectedConfiguration M f).deletedLines ↔
      a = M d true ∨ a = f (d, false) ∨ a = f (d, true) := by
  simp only [Configuration.deletedLines, Configuration.splitLines,
    selectedConfiguration, retainedChoice_line, constituent,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, Prod.mk.injEq]
  constructor
  · rintro (⟨e, b, he, ha⟩ | ⟨e, he, ha⟩)
    · subst e
      cases b
      · exact Or.inr (Or.inl ha.symm)
      · exact Or.inr (Or.inr ha.symm)
    · subst e
      exact Or.inl ha.symm
  · rintro (h | h | h)
    · exact Or.inr ⟨d, rfl, h.symm⟩
    · exact Or.inl ⟨d, false, rfl, h.symm⟩
    · exact Or.inl ⟨d, true, rfl, h.symm⟩

theorem selected_deletedLines_eq_assemble (M : MergedPairs F) (f : SplitOffsets F) :
    (selectedConfiguration M f).deletedLines =
      DeletionCoordinates.assemble
        (fun d => Finset.univ.image (roles (fun d => M d true, f) d)) := by
  ext l
  obtain ⟨d, a⟩ := l
  rw [mem_selected_deletedLines, DeletionCoordinates.mem_assemble]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (h | h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
  · rintro ⟨j, hj⟩
    fin_cases j <;> simp_all [roles]

theorem selected_deletedLines_eq_iff (M : MergedPairs F) (f : SplitOffsets F)
    (D : Finset (Line F)) :
    (selectedConfiguration M f).deletedLines = D ↔
      ∀ d, Finset.univ.image (roles (fun d => M d true, f) d) =
        DeletionCoordinates.fiber D d := by
  rw [selected_deletedLines_eq_assemble]
  constructor
  · intro h
    have hf := congrArg DeletionCoordinates.fiber h
    simpa only [DeletionCoordinates.fiber_assemble, funext_iff] using hf
  · intro h
    rw [show (fun d => Finset.univ.image (roles (fun d => M d true, f) d)) =
      DeletionCoordinates.fiber D from funext h]
    exact DeletionCoordinates.assemble_fiber D

theorem jointMass_eq_uniform_average (κ : SelectedDeletion.Kernel F)
    (E : MergedPairs F → SelectedDeletion.Output F → Prop) [∀ M f, Decidable (E M f)] :
    SelectedDeletion.jointMass κ E =
      (∑ M, ∑ f, if E M f then κ M f else 0) / Fintype.card (MergedPairs F) := by
  classical
  unfold SelectedDeletion.jointMass
  simp only [offsetLaw, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  simp only [div_eq_mul_inv, Finset.mul_sum, mul_comm]
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : E M f <;> simp [h]

omit [Field F] in

theorem card_mergedPairs :
    Fintype.card (MergedPairs F) =
      Fintype.card (SingleOffsets F) * Fintype.card (SingleOffsets F) := by
  rw [← Fintype.card_congr (offsetPairEquiv (F := F)), Fintype.card_prod]

theorem sum_fiberMass {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (κ : U → V → W → ℝ) :
    (∑ v, ∑ w, UniformKernel.fiberMass κ v w) =
      (∑ u, ∑ v, ∑ w, κ u v w) /
        ((Fintype.card U : ℝ) * Fintype.card V) := by
  simp only [UniformKernel.fiberMass, ← Finset.sum_div]
  congr 1
  calc
    (∑ v, ∑ w, ∑ u, κ u v w) = ∑ v, ∑ u, ∑ w, κ u v w := by
      apply Finset.sum_congr rfl
      intro v _
      exact Finset.sum_comm
    _ = ∑ u, ∑ v, ∑ w, κ u v w := Finset.sum_comm

theorem deletionJointMass_eq_fiber_sum (κ : SelectedDeletion.Kernel F)
    (D : DeletionSet F 3) :
    SelectedDeletion.deletionJointMass κ D =
      ∑ ω : SingleOffsets F × SplitOffsets F,
        if (∀ d, Finset.univ.image (roles ω d) = DeletionCoordinates.fiber D.val d) then
          UniformKernel.fiberMass
            (fun m₀ m₁ f => κ (offsetPairEquiv (m₀, m₁)) f) ω.1 ω.2 else 0 := by
  classical
  rw [SelectedDeletion.deletionJointMass, jointMass_eq_uniform_average]
  change (∑ M, ∑ f, if (selectedConfiguration M f).deletedLines = D.val then κ M f else 0) /
    (Fintype.card (MergedPairs F) : ℝ) = _
  rw [← (offsetPairEquiv (F := F)).sum_comp
    (fun M => ∑ f, if (selectedConfiguration M f).deletedLines = D.val then κ M f else 0)]
  rw [Fintype.sum_prod_type]
  simp_rw [selected_deletedLines_eq_iff]
  rw [card_mergedPairs, Nat.cast_mul, Fintype.sum_prod_type]
  let P := fun m₁ f => ∀ d, Finset.univ.image (roles (m₁, f) d) = DeletionCoordinates.fiber D.val d
  let W := fun m₀ m₁ f => κ (offsetPairEquiv (m₀, m₁)) f
  change (∑ m₀, ∑ m₁, ∑ f, if P m₁ f then W m₀ m₁ f else 0) /
    ((Fintype.card (SingleOffsets F) : ℝ) * Fintype.card (SingleOffsets F)) =
    ∑ m₁, ∑ f, if P m₁ f then UniformKernel.fiberMass W m₁ f else 0
  rw [← sum_fiberMass (fun m₀ m₁ f => if P m₁ f then W m₀ m₁ f else 0)]
  apply Finset.sum_congr rfl
  intro m₁ _
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : P m₁ f <;> simp [UniformKernel.fiberMass, h]

end Balanced.SelectedDeletionCoordinates

end OAI
