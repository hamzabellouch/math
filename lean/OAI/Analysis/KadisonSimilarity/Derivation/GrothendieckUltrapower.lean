import OAI.Analysis.KadisonSimilarity.Derivation.NormAttainingGrothendieck
import OAI.Analysis.NuclearUltrapower.HilbertUltraproduct

namespace OAI

/-! Bounded families turn approximate unitary norm attainment into exact
attainment. The source is the ordinary bounded product C-star algebra; only
the Hilbert target needs an ultraproduct. -/

noncomputable section
namespace KadisonSimilarity
open NuclearUltrapower Filter
open scoped ENNReal Topology ComplexOrder

variable {B H : Type*} [CStarAlgebra B] [Nontrivial B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Constants in the bounded product algebra. -/
def grothendieckConstant : B →⋆ₐ[ℂ] lp (fun _ : ℕ => B) ∞ where
  toFun b := ⟨fun _ => b, memℓp_infty ⟨‖b‖, by rintro _ ⟨i, rfl⟩; exact le_rfl⟩⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  commutes' _ := rfl

@[simp] theorem grothendieckConstant_apply (b : B) (i : ℕ) :
    grothendieckConstant b i = b := rfl

/-- Coordinatewise application, with the ultralimit seminorm on its target. -/
def grothendieckFamilyLinear (ω : Ultrafilter ℕ) (T : B →L[ℂ] H) :
    lp (fun _ : ℕ => B) ∞ →ₗ[ℂ] UltraPreHilbert (fun _ : ℕ => H) ω where
  toFun X := (⟨fun i => T (X i), memℓp_infty ⟨‖T‖ * ‖X‖, by
    rintro _ ⟨i, rfl⟩
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm ENNReal.top_ne_zero X i) (norm_nonneg T))⟩⟩ :
        lp (fun _ : ℕ => H) ∞)
  map_add' X Y := by apply Subtype.ext; funext i; exact map_add T _ _
  map_smul' c X := by apply Subtype.ext; funext i; exact map_smul T _ _

omit [Nontrivial B] in
@[simp] theorem grothendieckFamilyLinear_apply (ω : Ultrafilter ℕ) (T : B →L[ℂ] H)
    (X : lp (fun _ : ℕ => B) ∞) (i : ℕ) :
    UltraPreHilbert.family ω (grothendieckFamilyLinear ω T X) i = T (X i) := rfl

/-- The family map into the completed Hilbert ultraproduct. -/
def grothendieckFamilyMap (ω : Ultrafilter ℕ) (T : B →L[ℂ] H) :
    lp (fun _ : ℕ => B) ∞ →L[ℂ] HilbertUltraproduct (fun _ : ℕ => H) ω :=
  UniformSpace.Completion.toComplₗᵢ.toContinuousLinearMap.comp
    ((grothendieckFamilyLinear ω T).mkContinuous ‖T‖ (fun X => by
      apply le_of_tendsto (UltraPreHilbert.norm_tendsto ω _)
      exact Eventually.of_forall fun i =>
        (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm ENNReal.top_ne_zero X i) (norm_nonneg T))))

@[simp] theorem grothendieckFamilyMap_apply (ω : Ultrafilter ℕ) (T : B →L[ℂ] H)
    (X : lp (fun _ : ℕ => B) ∞) :
    grothendieckFamilyMap ω T X =
      (grothendieckFamilyLinear ω T X : HilbertUltraproduct (fun _ : ℕ => H) ω) := rfl

theorem grothendieckFamilyMap_norm_le (ω : Ultrafilter ℕ) (T : B →L[ℂ] H) :
    ‖grothendieckFamilyMap ω T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro X
  simp only [grothendieckFamilyMap_apply, UniformSpace.Completion.norm_coe]
  apply le_of_tendsto (UltraPreHilbert.norm_tendsto ω _)
  exact Eventually.of_forall fun i => (T.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero X i) (norm_nonneg T))

theorem grothendieckFamilyMap_norm_tendsto (ω : Ultrafilter ℕ) (T : B →L[ℂ] H)
    (X : lp (fun _ : ℕ => B) ∞) :
    Tendsto (fun i => ‖T (X i)‖) (ω : Filter ℕ) (𝓝 ‖grothendieckFamilyMap ω T X‖) := by
  simpa only [grothendieckFamilyMap_apply, UniformSpace.Completion.norm_coe,
    grothendieckFamilyLinear_apply] using
      UltraPreHilbert.norm_tendsto ω (grothendieckFamilyLinear ω T X)

@[simp] theorem grothendieckFamilyMap_constant_norm (ω : Ultrafilter ℕ)
    (T : B →L[ℂ] H) (b : B) :
    ‖grothendieckFamilyMap ω T (grothendieckConstant b)‖ = ‖T b‖ :=
  tendsto_nhds_unique (grothendieckFamilyMap_norm_tendsto ω T (grothendieckConstant b))
    tendsto_const_nhds

/-- A bounded family of unitaries is unitary in the bounded product. -/
def grothendieckUnitaryFamily (u : ℕ → unitary B) : unitary (lp (fun _ : ℕ => B) ∞) :=
  ⟨⟨fun i => u i, memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    exact (CStarRing.norm_coe_unitary (u i)).le⟩⟩, by
      constructor <;> apply Subtype.ext <;> funext i
      · exact Unitary.star_mul_self_of_mem (u i).prop
      · exact Unitary.mul_star_self_of_mem (u i).prop⟩

@[simp] theorem grothendieckUnitaryFamily_apply (u : ℕ → unitary B) (i : ℕ) :
    (grothendieckUnitaryFamily u : lp (fun _ : ℕ => B) ∞) i = u i := rfl

local instance : CStarAlgebra (lp (fun _ : ℕ => B) ∞) where

local instance : Nontrivial (lp (fun _ : ℕ => B) ∞) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have he := congrArg (fun X : lp (fun _ : ℕ => B) ∞ => X 0) h
  exact zero_ne_one he

section Positive
variable [PartialOrder B] [StarOrderedRing B]

local instance : PartialOrder (lp (fun _ : ℕ => B) ∞) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (lp (fun _ : ℕ => B) ∞) := CStarAlgebra.spectralOrderedRing _

/-- Restrict a positive functional on bounded families to the constants. -/
def grothendieckRestrict (f : lp (fun _ : ℕ => B) ∞ →ₚ[ℂ] ℂ) : B →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (f.toLinearMap.comp grothendieckConstant.toLinearMap) (fun b hb => by
    obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
    change 0 ≤ f (grothendieckConstant (star c * c))
    rw [map_mul, map_star]
    exact f.map_nonneg (star_mul_self_nonneg _))

@[simp] theorem grothendieckRestrict_apply (f : lp (fun _ : ℕ => B) ∞ →ₚ[ℂ] ℂ) (b : B) :
    grothendieckRestrict f b = f (grothendieckConstant b) := rfl

omit [PartialOrder B] [StarOrderedRing B] in
/-- The norm of a unitary family is attained at the limiting map. -/
theorem grothendieckFamily_attains (T : B →L[ℂ] H) (u : ℕ → unitary B)
    (hu : Tendsto (fun n => ‖T (u n : B)‖) atTop (𝓝 1)) :
    ‖grothendieckFamilyMap (Ultrafilter.of atTop) T
      (grothendieckUnitaryFamily u : lp (fun _ : ℕ => B) ∞)‖ = 1 :=
  tendsto_nhds_unique
    (grothendieckFamilyMap_norm_tendsto (Ultrafilter.of atTop) T (grothendieckUnitaryFamily u))
    (hu.mono_left (Ultrafilter.of_le _))

omit [PartialOrder B] [StarOrderedRing B] in
/-- Apply the proved norm-attaining theorem inside the bounded product. -/
theorem grothendieckFamily_states (T : B →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (u : ℕ → unitary B)
    (hu : Tendsto (fun n => ‖T (u n : B)‖) atTop (𝓝 1)) :
    ∃ f g : lp (fun _ : ℕ => B) ∞ →ₚ[ℂ] ℂ, f 1 = 1 ∧ g 1 = 1 ∧
      ∀ X, ‖grothendieckFamilyMap (Ultrafilter.of atTop) T X‖ ^ 2 ≤
        (f (star X * X)).re + (g (X * star X)).re := by
  have hS : ‖grothendieckFamilyMap (Ultrafilter.of atTop) T‖ ≤ 1 :=
    (grothendieckFamilyMap_norm_le (Ultrafilter.of atTop) T).trans hT
  have hunit := grothendieckFamily_attains T u hu
  exact unitaryNormAttaining_grothendieck
    (A := lp (fun _ : ℕ => B) ∞)
    (H := HilbertUltraproduct (fun _ : ℕ => H) (Ultrafilter.of atTop))
    (grothendieckFamilyMap (Ultrafilter.of atTop) T) hS
    (grothendieckUnitaryFamily u) hunit

/-- Approximate norm attainment at unitaries suffices for the exact two-state inequality. -/
theorem approximateUnitary_grothendieck (T : B →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (u : ℕ → unitary B)
    (hu : Tendsto (fun n => ‖T (u n : B)‖) atTop (𝓝 1)) :
    ∃ f g : B →ₚ[ℂ] ℂ, f 1 = 1 ∧ g 1 = 1 ∧
      ∀ b, ‖T b‖ ^ 2 ≤ (f (star b * b)).re + (g (b * star b)).re := by
  obtain ⟨f, g, hf, hg, hfg⟩ := grothendieckFamily_states T hT u hu
  refine ⟨grothendieckRestrict f, grothendieckRestrict g, ?_, ?_, fun b => ?_⟩
  · change f (grothendieckConstant 1) = 1
    exact (congrArg f (map_one grothendieckConstant)).trans hf
  · change g (grothendieckConstant 1) = 1
    exact (congrArg g (map_one grothendieckConstant)).trans hg
  · have h := hfg (grothendieckConstant b)
    rw [grothendieckFamilyMap_constant_norm] at h
    change ‖T b‖ ^ 2 ≤ (f (grothendieckConstant (star b * b))).re +
      (g (grothendieckConstant (b * star b))).re
    simpa only [map_mul, map_star] using h

end Positive

end KadisonSimilarity

end

end OAI
