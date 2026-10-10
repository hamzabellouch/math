import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum
import OAI.AlgebraicGeometry.PlaneCurves.Automorphic

namespace OAI

/-!
# Evaluation of cubic theta sections
-/

section

/-!
# Evaluation and first jets on genuine multiplier sections
-/

noncomputable section

namespace Nagata.W07

open Nagata.W08

/-- Evaluation in the actual covering-space frame. -/
def sectionEval (τ : ℂ) (n : ℤ) (γ z : ℂ) :
    automorphicSections τ n γ →ₗ[ℂ] ℂ where
  toFun f := f.val z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem sectionEval_apply (τ : ℂ) (n : ℤ) (γ z : ℂ)
    (f : automorphicSections τ n γ) : sectionEval τ n γ z f = f.val z := rfl

/-- Actual complex derivative at a point of the punctured plane. -/
def sectionDeriv (τ : ℂ) (n : ℤ) (γ : ℂ) {z : ℂ} (hz : z ≠ 0) :
    automorphicSections τ n γ →ₗ[ℂ] ℂ where
  toFun f := deriv f.val z
  map_add' f g := deriv_add (f.property.2.1 z hz) (g.property.2.1 z hz)
  map_smul' c f := deriv_const_mul c (f.property.2.1 z hz)

@[simp] theorem sectionDeriv_apply (τ : ℂ) (n : ℤ) (γ : ℂ) {z : ℂ}
    (hz : z ≠ 0) (f : automorphicSections τ n γ) :
    sectionDeriv τ n γ hz f = deriv f.val z := rfl

/-- Value and actual first derivative in one fixed local frame. -/
def sectionFirstJet (τ : ℂ) (n : ℤ) (γ : ℂ) {z : ℂ} (hz : z ≠ 0) :
    automorphicSections τ n γ →ₗ[ℂ] ℂ × ℂ :=
  (sectionEval τ n γ z).prod (sectionDeriv τ n γ hz)

/-- Values at two specified covering points. -/
def sectionTwoEval (τ : ℂ) (n : ℤ) (γ z w : ℂ) :
    automorphicSections τ n γ →ₗ[ℂ] ℂ × ℂ :=
  (sectionEval τ n γ z).prod (sectionEval τ n γ w)

@[simp] theorem mem_sectionEval_ker (τ : ℂ) (n : ℤ) (γ z : ℂ)
    (f : automorphicSections τ n γ) :
    f ∈ LinearMap.ker (sectionEval τ n γ z) ↔ f.val z = 0 := Iff.rfl

@[simp] theorem mem_sectionTwoEval_ker (τ : ℂ) (n : ℤ) (γ z w : ℂ)
    (f : automorphicSections τ n γ) :
    f ∈ LinearMap.ker (sectionTwoEval τ n γ z w) ↔ f.val z = 0 ∧ f.val w = 0 := by
  change (f.val z, f.val w) = (0, 0) ↔ _
  simp only [Prod.mk.injEq]

@[simp] theorem mem_sectionFirstJet_ker (τ : ℂ) (n : ℤ) (γ : ℂ) {z : ℂ}
    (hz : z ≠ 0) (f : automorphicSections τ n γ) :
    f ∈ LinearMap.ker (sectionFirstJet τ n γ hz) ↔
      f.val z = 0 ∧ deriv f.val z = 0 := by
  change (f.val z, deriv f.val z) = (0, 0) ↔ _
  simp only [Prod.mk.injEq]

/-- Rank-nullity gives surjectivity when the actual kernel has the expected codimension. -/
theorem linearMap_surjective_of_kernel_codimension
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (L : V →ₗ[ℂ] W)
    (hdim : Module.finrank ℂ (LinearMap.ker L) + Module.finrank ℂ W =
      Module.finrank ℂ V) : Function.Surjective L := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have hr := L.finrank_range_add_finrank_ker
  omega

/-- Dimension three and a two-dimensional vanishing kernel exclude a base point. -/
theorem cubic_eval_surjective (τ γ z : ℂ)
    (h3 : Module.finrank ℂ (automorphicSections τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    Function.Surjective (sectionEval τ 3 γ z) := by
  let : FiniteDimensional ℂ (automorphicSections τ 3 γ) :=
    FiniteDimensional.of_finrank_pos (by omega)
  apply linearMap_surjective_of_kernel_codimension
  simp [h3, hker]

theorem cubic_exists_section_eval_one (τ γ z : ℂ)
    (h3 : Module.finrank ℂ (automorphicSections τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    ∃ f : automorphicSections τ 3 γ, f.val z = 1 :=
  cubic_eval_surjective τ γ z h3 hker 1

/-- A one-dimensional simultaneous vanishing kernel allows independent values. -/
theorem cubic_twoEval_surjective (τ γ z w : ℂ)
    (h3 : Module.finrank ℂ (automorphicSections τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionTwoEval τ 3 γ z w)) = 1) :
    Function.Surjective (sectionTwoEval τ 3 γ z w) := by
  let : FiniteDimensional ℂ (automorphicSections τ 3 γ) :=
    FiniteDimensional.of_finrank_pos (by omega)
  apply linearMap_surjective_of_kernel_codimension
  simp [Module.finrank_prod, h3, hker]

theorem cubic_exists_section_separating (τ γ z w : ℂ)
    (h3 : Module.finrank ℂ (automorphicSections τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionTwoEval τ 3 γ z w)) = 1) :
    ∃ f : automorphicSections τ 3 γ, f.val z = 1 ∧ f.val w = 0 := by
  obtain ⟨f, hf⟩ := cubic_twoEval_surjective τ γ z w h3 hker (1, 0)
  exact ⟨f, Prod.mk.inj hf⟩

/-- The double-point kernel of dimension one implies full first-jet separation. -/
theorem cubic_firstJet_surjective (τ γ : ℂ) {z : ℂ} (hz : z ≠ 0)
    (h3 : Module.finrank ℂ (automorphicSections τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionFirstJet τ 3 γ hz)) = 1) :
    Function.Surjective (sectionFirstJet τ 3 γ hz) := by
  let : FiniteDimensional ℂ (automorphicSections τ 3 γ) :=
    FiniteDimensional.of_finrank_pos (by omega)
  apply linearMap_surjective_of_kernel_codimension
  simp [Module.finrank_prod, h3, hker]

/-- An actual ratio of genuine sections is a local coordinate with derivative one.
The denominator is chosen to have value one, so the quotient is holomorphic near the point. -/
theorem cubic_exists_ratio_deriv_one (τ γ : ℂ) {z : ℂ} (hz : z ≠ 0)
    (h3 : Module.finrank ℂ (automorphicSections τ 3 γ) = 3)
    (hker1 : Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (hker2 : Module.finrank ℂ (LinearMap.ker (sectionFirstJet τ 3 γ hz)) = 1) :
    ∃ f g : automorphicSections τ 3 γ,
      f.val z = 0 ∧ g.val z = 1 ∧ deriv f.val z = 1 ∧
        deriv (fun w => f.val w / g.val w) z = 1 := by
  obtain ⟨f, hf⟩ := cubic_firstJet_surjective τ γ hz h3 hker2 (0, 1)
  have hf0 : f.val z = 0 := congrArg Prod.fst hf
  have hfd : deriv f.val z = 1 := congrArg Prod.snd hf
  obtain ⟨g, hg⟩ := cubic_exists_section_eval_one τ γ z h3 hker1
  refine ⟨f, g, hf0, hg, hfd, ?_⟩
  have hgn : g.val z ≠ 0 := by rw [hg]; exact one_ne_zero
  have hd := ((f.property.2.1 z hz).hasDerivAt.fun_div
    (g.property.2.1 z hz).hasDerivAt hgn).deriv
  simpa [hf0, hg, hfd] using hd

end Nagata.W07

end
end

end OAI
