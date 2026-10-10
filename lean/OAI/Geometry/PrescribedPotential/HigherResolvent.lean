import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedResolvent
import OAI.Geometry.PrescribedPotential.PatchCutoffs

namespace OAI

/-! Higher Resolvent. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)

lemma lower_lower {s t r : ℝ} (hst : t ≤ s) (htr : r ≤ t) (u : D.Sobolev s) :
    D.lower t r (D.lower s t u) = D.lower s r u :=
  congrArg (fun L : D.Sobolev s →L[ℝ] D.Sobolev r => L u) (D.lower_comp hst htr)

end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

 

theorem errorInverse_order (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (k : ℕ) : ∃ R : D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev (k : ℝ),
      ∀ f, D.localizers.lower (k : ℝ) 0 (R f) =
        D.errorInverse m hm he (D.localizers.lower (k : ℝ) 0 f) := by
  induction k with
  | zero =>
    rw [Nat.cast_zero]
    refine ⟨D.errorInverse m hm he, fun f => ?_⟩
    simp only [D.localizers.lower_self, ContinuousLinearMap.id_apply]
  | succ k ih =>
    rw [Nat.cast_succ]
    obtain ⟨R, hR⟩ := ih
    let U := D.localizers.extendCore (k : ℝ) ((k : ℝ)+1) (D.error m hm)
    let R' : D.localizers.Sobolev ((k : ℝ)+1) →L[ℝ] D.localizers.Sobolev ((k : ℝ)+1) :=
      ContinuousLinearMap.id ℝ _ + U ∘L R ∘L D.localizers.lower ((k : ℝ)+1) (k : ℝ)
    refine ⟨R', fun f => ?_⟩
    change D.localizers.lower ((k : ℝ)+1) 0
      (f + U (R (D.localizers.lower ((k : ℝ)+1) (k : ℝ) f))) = _
    rw [map_add, D.localizers.extendCore_compat (Nat.cast_nonneg k) (by positivity : (0:ℝ) ≤ (k : ℝ)+1)
      (D.error m hm) (D.error_bound_integer m hm k) (D.error_bound_zero m hm), hR,
      D.localizers.lower_lower (by linarith : (k : ℝ) ≤ (k : ℝ)+1) (Nat.cast_nonneg k)]
    have h := D.errorInverse_equation m hm he (D.localizers.lower ((k : ℝ)+1) 0 f)
    change _ = D.errorInverse m hm he (D.localizers.lower ((k : ℝ)+1) 0 f)
    exact (sub_eq_iff_eq_add.mp h).symm

 
theorem completedResolvent_order (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (k : ℕ) : ∃ R : D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev ((k : ℝ)+2),
      ∀ f, D.localizers.lower ((k : ℝ)+2) 2 (R f) =
        D.completedResolvent m hm he (D.localizers.lower (k : ℝ) 0 f) := by
  obtain ⟨R, hR⟩ := D.errorInverse_order m hm he k
  refine ⟨D.localizers.extendCore (k : ℝ) ((k : ℝ)+2) (D.parametrix m hm) ∘L R, fun f => ?_⟩
  simp only [ContinuousLinearMap.comp_apply]
  rw [D.localizers.extendCore_compat (Nat.cast_nonneg k)
    (by linarith [Nat.cast_nonneg (α := ℝ) k] : (2:ℝ) ≤ (k : ℝ)+2)
    (D.parametrix m hm) (D.parametrix_bound m hm k) (D.completedParametrix_bound m hm), hR]
  rfl

end GluingData
end GlobalElliptic

end
end

end OAI
