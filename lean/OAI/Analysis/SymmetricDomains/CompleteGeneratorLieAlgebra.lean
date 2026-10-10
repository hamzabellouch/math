import Mathlib
import OAI.Analysis.SymmetricDomains.PushForwardGeneratorDeriv

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd Γ hhol

theorem IsCompleteGenerator.lieBracket {X Y : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y) :
    IsCompleteGenerator U (VectorField.lieBracket ℂ X Y) := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  let S := completeGeneratorSpace hU hc hbd Γ hhol
  let Z : ℝ → Affine n → Affine n := fun t =>
    t⁻¹ • (pushForwardGenerator (a t) Y-pushForwardGenerator (a 0) Y)
  have hZ : ∀ t, Z t∈S := by
    intro t
    exact S.smul_mem t⁻¹ (S.sub_mem (hY.pushForward hU hbd (a t)) (hY.pushForward hU hbd (a 0)))
  have hz : IsCompleteGenerator U (-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y) := by
    apply isCompleteGenerator_of_tendsto hU hc hbd Γ hhol (l := 𝓝[≠] (0:ℝ)) Z _ (Eventually.of_forall hZ)
    intro x
    have hd : HasDerivAt (fun t : ℝ => pushForwardGenerator (a t) Y x)
        (-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y x) 0 := by
      by_cases hx : x∈U
      · exact pushForwardGenerator_hasDerivAt_zero hU hbd a ha ha0 ham Y
          (hY.analyticOnNhd hU hbd) x hx
      · have hbr := VectorField.lieBracket_eq_zero_of_eq_zero (𝕜 := ℂ)
          (infinitesimalGenerator_of_not_mem a hx) (hY.eq_zero_of_not_mem hx)
        simpa only [pushForwardGenerator,dite_eq_right hx,hbr,neg_zero] using hasDerivAt_const (0:ℝ) (0 : Affine n)
    apply hd.tendsto_slope.congr'
    filter_upwards [] with t
    change (t-(0:ℝ))⁻¹ • (pushForwardGenerator (a t) Y x - pushForwardGenerator (a 0) Y x) =
      t⁻¹ • (pushForwardGenerator (a t) Y x - pushForwardGenerator (a 0) Y x)
    rw [sub_zero]
  have hz' : -(-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y)∈S := S.neg_mem hz
  change IsCompleteGenerator U (-(-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y)) at hz'
  simpa only [neg_neg] using hz'

def completeGeneratorBracket (X Y : completeGeneratorSpace hU hc hbd Γ hhol) :
    completeGeneratorSpace hU hc hbd Γ hhol :=
  ⟨VectorField.lieBracket ℂ X.val Y.val,X.property.lieBracket hU hc hbd Γ hhol Y.property⟩

instance completeGeneratorLieRing : LieRing (completeGeneratorSpace hU hc hbd Γ hhol) where
  bracket := completeGeneratorBracket hU hc hbd Γ hhol
  add_lie X Y Z := by
    apply Subtype.ext
    funext x
    change VectorField.lieBracket ℂ (X.val+Y.val) Z.val x =
      VectorField.lieBracket ℂ X.val Z.val x + VectorField.lieBracket ℂ Y.val Z.val x
    by_cases hx : x∈U
    · exact VectorField.lieBracket_add_left ((X.property.analyticOnNhd hU hbd) x hx).differentiableAt
        ((Y.property.analyticOnNhd hU hbd) x hx).differentiableAt
    · simp only [VectorField.lieBracket,Pi.add_apply,X.property.eq_zero_of_not_mem hx,
        Y.property.eq_zero_of_not_mem hx,Z.property.eq_zero_of_not_mem hx,add_zero,map_zero,sub_zero]
  lie_add X Y Z := by
    apply Subtype.ext
    funext x
    change VectorField.lieBracket ℂ X.val (Y.val+Z.val) x =
      VectorField.lieBracket ℂ X.val Y.val x + VectorField.lieBracket ℂ X.val Z.val x
    by_cases hx : x∈U
    · exact VectorField.lieBracket_add_right ((Y.property.analyticOnNhd hU hbd) x hx).differentiableAt
        ((Z.property.analyticOnNhd hU hbd) x hx).differentiableAt
    · simp only [VectorField.lieBracket,Pi.add_apply,X.property.eq_zero_of_not_mem hx,
        Y.property.eq_zero_of_not_mem hx,Z.property.eq_zero_of_not_mem hx,add_zero,map_zero,sub_zero]
  lie_self X := by
    apply Subtype.ext
    exact VectorField.lieBracket_self
  leibniz_lie X Y Z := by
    apply Subtype.ext
    funext x
    change VectorField.lieBracket ℂ X.val (VectorField.lieBracket ℂ Y.val Z.val) x =
      VectorField.lieBracket ℂ (VectorField.lieBracket ℂ X.val Y.val) Z.val x +
      VectorField.lieBracket ℂ Y.val (VectorField.lieBracket ℂ X.val Z.val) x
    by_cases hx : x∈U
    · exact VectorField.leibniz_identity_lieBracket (le_top : minSmoothness ℂ 2 ≤ ⊤)
        ((X.property.analyticOnNhd hU hbd) x hx).contDiffAt
        ((Y.property.analyticOnNhd hU hbd) x hx).contDiffAt
        ((Z.property.analyticOnNhd hU hbd) x hx).contDiffAt
    · simp only [VectorField.lieBracket,X.property.eq_zero_of_not_mem hx,
        Y.property.eq_zero_of_not_mem hx,Z.property.eq_zero_of_not_mem hx,map_zero,sub_zero,add_zero]

instance completeGeneratorLieAlgebra : LieAlgebra ℝ (completeGeneratorSpace hU hc hbd Γ hhol) where
  lie_smul c X Y := by
    apply Subtype.ext
    funext x
    change VectorField.lieBracket ℂ X.val (c • Y.val) x = c • VectorField.lieBracket ℂ X.val Y.val x
    by_cases hx : x∈U
    · simp only [VectorField.lieBracket,Pi.smul_apply,
        fderiv_const_smul ((Y.property.analyticOnNhd hU hbd) x hx).differentiableAt,
        smul_apply,ContinuousLinearMap.map_smul_of_tower,smul_sub]
    · simp only [VectorField.lieBracket,Pi.smul_apply,X.property.eq_zero_of_not_mem hx,
        Y.property.eq_zero_of_not_mem hx,smul_zero,map_zero,sub_zero]

end Biholomorph
end Release061

end

end OAI
