import OAI.Analysis.LipschitzFree.RenormingModel
import OAI.Analysis.LipschitzFree.Coefficients
import OAI.Analysis.LipschitzFree.BlockBAP
import OAI.Analysis.LipschitzFree.WedgeApproximation

namespace OAI

/-!
# Equivalent complete norms on real ℓ¹ with quantitative BAP obstructions
-/

noncomputable section
open scoped BigOperators ENNReal Classical

namespace DiscreteFree

theorem hasBAP_of_linearIsometryEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : E ≃ₗᵢ[ℝ] F) (Λ : ℝ) (h : HasBAP F Λ) : HasBAP E Λ := by
  exact hasBAP_of_contractive_retract
    I.toLinearIsometry.toContinuousLinearMap I.symm.toLinearIsometry.toContinuousLinearMap
    I.toLinearIsometry.norm_toContinuousLinearMap_le
    I.symm.toLinearIsometry.norm_toContinuousLinearMap_le
    (by ext u; exact I.symm_apply_apply u) Λ h

theorem hasBAP_linearIsometryEquiv_iff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : E ≃ₗᵢ[ℝ] F) (Λ : ℝ) : HasBAP E Λ ↔ HasBAP F Λ :=
  ⟨hasBAP_of_linearIsometryEquiv I.symm Λ, hasBAP_of_linearIsometryEquiv I Λ⟩

end DiscreteFree
end

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

theorem real_l1_quantitative_renorming : RealL1RenormingStatement := by
  intro p hp
  let : Fact (0 < BlockParameters.R p) := ⟨BlockParameters.R_pos hp⟩
  let o := BlockConstruction.base p
  let sep := BlockConstruction.separation p
  have hb (x : BlockConstruction.Block p) : dist x o ≤ blockBound p := by
    simpa only [BlockParameters.B_formula] using BlockConstruction.diameter p x o
  have hB : 0 ≤ blockBound p := by dsimp [blockBound]; positivity
  let α := {x : BlockConstruction.Block p // x ≠ o}
  let : Infinite α := (Set.finite_singleton o).infinite_compl.to_subtype
  let : Encodable α := Encodable.ofCountable α
  let : Denumerable α := Denumerable.ofEncodableOfInfinite α
  let e : ℕ ≃ α := (Denumerable.eqv α).symm
  let J : RealL1 ≃L[ℝ] FreeSpace o := Coefficients.equiv o sep e (blockBound p) hb
  let A : RealL1 ≃ₗ[ℝ] FreeSpace o := J.toLinearEquiv
  let m : Module ℝ RealL1 := inferInstance
  let N : AddGroupNorm RealL1 :=
    { toFun := fun c => ‖J c‖
      map_zero' := by simp
      add_le' := fun c d => by simpa only [map_add] using norm_add_le (J c) (J d)
      neg' := fun c => by simp
      eq_zero_of_map_eq_zero' := fun c hc => J.injective (by simpa using hc) }
  refine ⟨N, ?_, ?_, ?_⟩
  · intro r c
    change ‖J (r • c)‖ = |r| * ‖J c‖
    rw [map_smul, norm_smul, Real.norm_eq_abs]
  · exact Coefficients.equiv_bounds o sep e (blockBound p) hb
  · let : NormedAddCommGroup RealL1 := N.toNormedAddCommGroup
    let s : NormedSpace ℝ RealL1 :=
      { toModule := m
        norm_smul_le := fun r c => by
          change ‖J (r • c)‖ ≤ ‖r‖ * ‖J c‖
          rw [map_smul, norm_smul] }
    refine ⟨s, rfl, ?_⟩
    let := s
    let I : RealL1 ≃ₗᵢ[ℝ] FreeSpace o :=
      { toLinearEquiv := A
        norm_map' := fun _ => rfl }
    have hgood : HasBAP (FreeSpace o) (2 * blockBound p) :=
      bounded_separated_hasBAP o sep (blockBound p) hB hb
    have hbad : ¬ HasBAP (FreeSpace o) (p : ℝ) :=
      BlockConstruction.noBAP p hp p le_rfl
    have hnewbad : ¬ HasBAP RealL1 (p : ℝ) := fun h =>
      hbad ((hasBAP_linearIsometryEquiv_iff I p).mp h)
    refine ⟨I.toIsometryEquiv.completeSpace,
      (hasBAP_linearIsometryEquiv_iff I _).mpr hgood, hnewbad, ?_⟩
    intro hp1
    simpa only [hp1, Nat.cast_one] using hnewbad

end DiscreteFree
end

end OAI
