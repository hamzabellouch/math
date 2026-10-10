import Mathlib
import OAI.Geometry.HyperbolicGroups.StarModelFurther
import OAI.Geometry.HyperbolicGroups.StarActual
import OAI.Geometry.HyperbolicGroups.ExtensionMargin

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

abbrev leafCount (support : R → Finset F) (U : Finset F) (e : F) (ξ : Var (B := B) U → A) :=
  BernoulliCandidates.count
    (fun σ => row support U (PinnedAssignments.extend (leafPins U e) ξ σ))
    (PinnedAssignments.candidates (field U) (leafPins U e) ξ)

abbrev extensionCount (support : R → Finset F) (U : Finset F) (j₀ : B) (ξ : Var (B := B) U → A) :=
  BernoulliCandidates.count
    (fun σ s => row support U (PinnedAssignments.extend (branchPins U j₀) ξ σ) (extPos support U j₀ s))
    (PinnedAssignments.candidates (field U) (branchPins U j₀) ξ)

omit [Fintype B] [Fintype A] [DecidableEq A] [Nonempty B] in
lemma branch_pin_fieldwise (U : Finset F) (j₀ : B) (ξ : Var (B := B) U → A) :
    PinnedAssignments.PinFieldwise (field U) (branchPins U j₀) ξ := by
  intro v hv w hw ht _
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hw
  simp only [field_coord] at ht
  exact congrArg (coord U j₀) ht

omit [Fintype F] [Fintype R] [Fintype B] [Fintype A]
    [DecidableEq R] [DecidableEq B] [DecidableEq A] in
lemma ext_injective (support : R → Finset F) (U : Finset F) (j₀ : B)
    (σ : Var (B := B) U → A) (hσ : PinnedAssignments.Fieldwise (field U) σ) :
    Function.Injective (fun s => row support U σ (extPos support U j₀ s)) :=
  (row_injective support U σ ((fieldwise_iff U σ).mp hσ)).comp (extPos_injective support U j₀)

omit [Fintype F] in
lemma ext_surcharge_le (support : R → Finset F) (U : Finset F) (j₀ : B) (c : R → ℝ)
    (hc : ∀ r, 0 ≤ c r) (J : Finset (ExtPos support U j₀)) :
    (∑ s ∈ J, c s.2.val) ≤ (Fintype.card B : ℝ) * ∑ r, c r := by
  have hsum : (∑ s ∈ J, c s.2.val) =
      ∑ s ∈ J.image (extPos support U j₀), c (array support U s) := by
    rw [Finset.sum_image (fun _ _ _ _ h => extPos_injective support U j₀ h)]
    rfl
  rw [hsum]
  exact sum_array_le support U c hc _

end StarModel
namespace IncidenceTemplate

/-- Named finite instances avoid repeatedly synthesizing the literal nested subtype. -/
instance instRowFintype : Fintype Row := inferInstance
instance instFieldFintype : Fintype Field := inferInstance

variable {B A : Type*} [Fintype B] [Fintype A] [DecidableEq B] [DecidableEq A]
  [Nonempty B] [Nonempty A]

lemma star_extension_actual_gap {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (U : Finset Field) (j₀ : B)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ pattern.exponent (U ∪ W) - pattern.exponent U)
    (J : Finset (StarModel.ExtPos rowSupport U j₀)) (hJ : J.Nonempty) :
    1 - (Fintype.card B : ℝ) * (β + 90 * δ) ≤
      (((J.biUnion (fun s => StarModel.rowSupport rowSupport U (StarModel.extPos rowSupport U j₀ s))) \ StarModel.branchPins U j₀).card : ℝ) -
        ∑ s ∈ J, actualRowCost α β δ s.2.val := by
  have hcrit := StarModel.extension_critical_gap pattern U j₀ gap J hJ
  have hc : (1 : ℝ) ≤
      (((J.biUnion (fun s => StarModel.rowSupport rowSupport U (StarModel.extPos rowSupport U j₀ s))) \ StarModel.branchPins U j₀).card : ℝ) -
        ∑ s ∈ J, (rowCost s.2.val : ℝ) := by exact_mod_cast hcrit
  have hs := StarModel.ext_surcharge_le rowSupport U j₀ (rowSurcharge α β δ) (rowSurcharge_nonneg ha hb hd) J
  rw [rowSurcharge_sum] at hs
  simp only [actualRowCost,Finset.sum_add_distrib]
  linarith

/-- Relative variance for the literal fieldwise-injective leaf count. The
alphabet size threshold and constants are independent of pinned letter values. -/
theorem leaf_variance_bound {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (hsmall : (Fintype.card B : ℝ) * (β + 90 * δ) ≤ 1 / 2)
    (U : Finset Field) (e : Field) (he : e ∉ U)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ pattern.exponent (U ∪ W) - pattern.exponent U)
    (ξ : StarModel.Var (B := B) U → A)
    (hξ : PinnedAssignments.PinFieldwise (StarModel.field U) (StarModel.leafPins U e) ξ)
    (hN : 4 * Fintype.card (StarModel.Var (B := B) U) ≤ Fintype.card A) :
    let hp := fun r => TableModel.powerProbability_mem
      (show (1 : ℝ) ≤ Fintype.card A by exact_mod_cast Fintype.card_pos (α := A)) (actualRowCost_nonneg ha hb hd r)
    let μ := TableModel.law rowSupport (fun r => (Fintype.card A : ℝ) ^ (-actualRowCost α β δ r)) hp
    let X := fun w => (StarModel.leafCount rowSupport U e ξ w : ℝ)
    μ.variance X ≤ Fintype.card (BernoulliCandidates.OverlapType (StarModel.Pos (B := B) rowSupport U)) *
      2 ^ Fintype.card (PinnedAssignments.Free (StarModel.leafPins (B := B) U e)) *
      (Fintype.card A : ℝ) ^ (-(1 / 2 : ℝ)) * μ.expect X ^ 2 := by
  apply PinnedAssignments.relative_variance (StarModel.field U) (StarModel.leafPins U e) ξ hξ hN
    (StarModel.row rowSupport U) (StarModel.rowSupport rowSupport U) (StarModel.read_row rowSupport U)
    (fun σ hσ => StarModel.row_injective rowSupport U σ ((StarModel.fieldwise_iff U σ).mp hσ))
    _ _ (fun s => actualRowCost α β δ (StarModel.array rowSupport U s)) (fun _ _ => rfl)
  intro J hJ
  have hh := star_leaf_actual_gap ha hb hd U e he gap J hJ
  linarith

/-- Unconditioned variance for the residual trials of an extension. The next
conditioning identity identifies this with variance given the fixed match. -/
theorem extension_variance_bound {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (hsmall : (Fintype.card B : ℝ) * (β + 90 * δ) ≤ 1 / 2)
    (U : Finset Field) (j₀ : B)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ pattern.exponent (U ∪ W) - pattern.exponent U)
    (ξ : StarModel.Var (B := B) U → A)
    (hN : 4 * Fintype.card (StarModel.Var (B := B) U) ≤ Fintype.card A) :
    let hp := fun r => TableModel.powerProbability_mem
      (show (1 : ℝ) ≤ Fintype.card A by exact_mod_cast Fintype.card_pos (α := A)) (actualRowCost_nonneg ha hb hd r)
    let μ := TableModel.law rowSupport (fun r => (Fintype.card A : ℝ) ^ (-actualRowCost α β δ r)) hp
    let X := fun w => (StarModel.extensionCount rowSupport U j₀ ξ w : ℝ)
    μ.variance X ≤ Fintype.card (BernoulliCandidates.OverlapType (StarModel.ExtPos rowSupport U j₀)) *
      2 ^ Fintype.card (PinnedAssignments.Free (StarModel.branchPins U j₀)) *
      (Fintype.card A : ℝ) ^ (-(1 / 2 : ℝ)) * μ.expect X ^ 2 := by
  apply PinnedAssignments.relative_variance (StarModel.field U) (StarModel.branchPins U j₀) ξ
    (StarModel.branch_pin_fieldwise U j₀ ξ) hN
    (fun σ s => StarModel.row rowSupport U σ (StarModel.extPos rowSupport U j₀ s))
    (fun s => StarModel.rowSupport rowSupport U (StarModel.extPos rowSupport U j₀ s))
    (fun σ τ s => StarModel.read_row rowSupport U σ τ (StarModel.extPos rowSupport U j₀ s))
    (StarModel.ext_injective rowSupport U j₀)
    _ _ (fun s => actualRowCost α β δ s.2.val) (fun _ _ => rfl)
  intro J hJ
  have hh := star_extension_actual_gap ha hb hd U j₀ gap J hJ
  linarith

end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
