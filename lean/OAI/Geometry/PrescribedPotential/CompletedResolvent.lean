import Mathlib
import OAI.Geometry.PrescribedPotential.ComplexOperator
import OAI.Geometry.PrescribedPotential.GlobalBounds
import OAI.Geometry.PrescribedPotential.GlobalError
import OAI.Geometry.PrescribedPotential.PatchCutoffs

namespace OAI

/-! Completed Resolvent. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)

 

lemma extendCore_compat {s t a b : ℝ} (has : a ≤ s) (hbt : b ≤ t)
    (T : Smooth A →ₗ[ℝ] Smooth A) (hT : D.BoundedCore s t T)
    (hB : D.BoundedCore a b T) (u : D.Sobolev s) :
    D.lower t b (D.extendCore s t T u) =
      D.extendCore a b T (D.lower s a u) := by
  have hS : D.BoundedCore s b T := hT.target_mono hbt
  rw [D.lower_extendCore hbt T hT hS, D.extendCore_lower has T hB hS]

 
def AllRegular (u : D.Sobolev 0) : Prop :=
  ∀ k : ℕ, ∃ v : D.Sobolev (k : ℝ), D.lower (k : ℝ) 0 v = u

lemma allRegular_embed (f : Smooth A) : D.AllRegular (D.embed 0 f) := by
  intro k
  exact ⟨D.embed (k : ℝ) f, D.lower_embed (Nat.cast_nonneg _) f⟩

lemma allRegular_of_gain (T : Smooth A →ₗ[ℝ] Smooth A)
    (h0 : D.BoundedCore 0 0 T)
    (hgain : ∀ k : ℕ, D.BoundedCore (k : ℝ) ((k : ℝ) + 1) T)
    (f : Smooth A) (u : D.Sobolev 0)
    (hu : u = D.embed 0 f + D.extendCore 0 0 T u) : D.AllRegular u := by
  intro k
  induction k with
  | zero =>
    rw [Nat.cast_zero]
    exact ⟨u, by rw [D.lower_self]; rfl⟩
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one]
    obtain ⟨v, hv⟩ := ih
    have h := D.extendCore_compat (Nat.cast_nonneg k)
      (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) T (hgain k) h0 v
    refine ⟨D.embed (k + 1 : ℝ) f + D.extendCore (k : ℝ) (k + 1 : ℝ) T v, ?_⟩
    rw [map_add, D.lower_embed (by positivity), h, hv, ← hu]

end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

 
def completedL : D.localizers.Sobolev 2 →L[ℝ] D.localizers.Sobolev 0 :=
  D.localizers.extendCore 2 0 (complexL g)

def shiftedOperator (m : ℝ) : D.localizers.Sobolev 2 →L[ℝ] D.localizers.Sobolev 0 :=
  (m^2 : ℝ) • D.localizers.lower 2 0 - D.completedL

def completedParametrix (m : ℝ) (hm : 1 ≤ m) :
    D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 2 :=
  D.localizers.extendCore 0 2 (D.parametrix m hm)

def completedError (m : ℝ) (hm : 1 ≤ m) :
    D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 0 :=
  D.localizers.extendCore 0 0 (D.error m hm)

lemma completedParametrix_bound (m : ℝ) (hm : 1 ≤ m) :
    D.localizers.BoundedCore 0 2 (D.parametrix m hm) := by
  have hb := D.parametrix_bound m hm 0
  rw [Nat.cast_zero, zero_add] at hb
  exact hb

lemma completedParametrix_equation (m : ℝ) (hm : 1 ≤ m) (u : D.localizers.Sobolev 0) :
    D.shiftedOperator m (D.completedParametrix m hm u) = u - D.completedError m hm u := by
  have he : D.shiftedOperator m ∘ D.completedParametrix m hm =
      fun u => u - D.completedError m hm u := by
    apply (D.localizers.embed_dense 0).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply, shiftedOperator, completedParametrix, completedL,
      completedError, _root_.sub_apply, _root_.smul_apply,
      D.localizers.extendCore_embed (D.completedParametrix_bound m hm),
      D.localizers.extendCore_embed D.complexL_bound,
      D.localizers.extendCore_embed (D.error_bound_zero m hm),
      D.localizers.lower_embed (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← map_smul, ← map_sub, D.parametrix_equation, map_sub]
  exact congr_fun he u

lemma exists_completedError_small :
    ∃ m : ℝ, ∃ hm : 1 ≤ m, ‖D.completedError m hm‖ < 1 := by
  obtain ⟨m, hm, q, hq, hq1, hb⟩ := D.exists_contractive_shift
  exact ⟨m, hm, (D.localizers.extendCore_norm hq hb).trans_lt hq1⟩

 

def errorInverse (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1) :
    D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 0 :=
  ↑((Units.oneSub (D.completedError m hm) he)⁻¹)

lemma errorInverse_equation (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (f : D.localizers.Sobolev 0) :
    D.errorInverse m hm he f - D.completedError m hm (D.errorInverse m hm he f) = f := by
  let U := Units.oneSub (D.completedError m hm) he
  change ((↑U : D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 0) * ↑U⁻¹) f = f
  rw [Units.mul_inv, _root_.one_apply_eq_self]

def completedResolvent (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1) :
    D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 2 :=
  D.completedParametrix m hm ∘L D.errorInverse m hm he

theorem completedResolvent_equation (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (f : D.localizers.Sobolev 0) :
    D.shiftedOperator m (D.completedResolvent m hm he f) = f := by
  rw [completedResolvent, ContinuousLinearMap.comp_apply, D.completedParametrix_equation,
    D.errorInverse_equation]

lemma errorInverse_regular (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (f : Smooth A) : D.localizers.AllRegular (D.errorInverse m hm he (D.localizers.embed 0 f)) := by
  apply D.localizers.allRegular_of_gain (D.error m hm) (D.error_bound_zero m hm)
    (D.error_bound_integer m hm) f
  exact sub_eq_iff_eq_add.mp (D.errorInverse_equation m hm he _)

lemma parametrix_regular (m : ℝ) (hm : 1 ≤ m) (u : D.localizers.Sobolev 0)
    (hu : D.localizers.AllRegular u) :
    D.localizers.AllRegular (D.localizers.lower 2 0 (D.completedParametrix m hm u)) := by
  intro k
  obtain ⟨v, hv⟩ := hu k
  have hb := D.parametrix_bound m hm k
  refine ⟨D.localizers.lower ((k : ℝ) + 2) (k : ℝ)
    (D.localizers.extendCore (k : ℝ) ((k : ℝ) + 2) (D.parametrix m hm) v), ?_⟩
  rw [← ContinuousLinearMap.comp_apply,
    D.localizers.lower_comp (by linarith : (k : ℝ) ≤ (k : ℝ) + 2) (Nat.cast_nonneg k)]
  rw [D.localizers.extendCore_compat (Nat.cast_nonneg k)
    (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2) _ hb
      ((D.completedParametrix_bound m hm).target_mono (by norm_num : (0 : ℝ) ≤ 2)), hv]
  exact (D.localizers.lower_extendCore (by norm_num : (0 : ℝ) ≤ 2) _
    (D.completedParametrix_bound m hm)
    ((D.completedParametrix_bound m hm).target_mono (by norm_num : (0 : ℝ) ≤ 2)) u).symm

theorem completedResolvent_regular (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (f : Smooth A) :
    D.localizers.AllRegular (D.localizers.lower 2 0
      (D.completedResolvent m hm he (D.localizers.embed 0 f))) :=
  D.parametrix_regular m hm _ (D.errorInverse_regular m hm he f)

end GluingData
end GlobalElliptic

end
end

end OAI
