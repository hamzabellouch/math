import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Group

namespace OAI

/-! # Coordinates separating a quotient and its kernel

A continuous section of the actual quotient map gives global coordinates.
The formulas retain the conjugation and section cocycle needed for product
Haar measure and the ideal-coordinate estimates.
-/

noncomputable section
namespace PolycyclicRecognition

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)

/-- The kernel component left after removing the chosen section. -/
def quotientSectionResidual (n : N) : π.ker :=
  ⟨n * (s (π n))⁻¹, by
    change π (n * (s (π n))⁻¹) = 1
    rw [map_mul, map_inv, hs, mul_inv_cancel]⟩

/-- Quotient coordinate first, followed by the actual kernel coordinate. -/
def quotientSectionHomeomorph : N ≃ₜ Q × π.ker := by
  let f : N → Q × π.ker := fun n => (π n, quotientSectionResidual π s hs n)
  let g : Q × π.ker → N := fun p => (p.2 : N) * s p.1
  have hfg (p : Q × π.ker) : f (g p) = p := by
    have hp : π p.2 = 1 := p.2.property
    apply Prod.ext
    · change π ((p.2 : N) * s p.1) = p.1
      rw [map_mul, hp, hs, one_mul]
    · apply Subtype.ext
      change ((p.2 : N) * s p.1) * (s (π ((p.2 : N) * s p.1)))⁻¹ = p.2
      rw [map_mul, hp, hs, one_mul]
      exact mul_inv_cancel_right _ _
  have hgf (n : N) : g (f n) = n := by
    change (n * (s (π n))⁻¹) * s (π n) = n
    simp
  refine
    { toFun := f
      invFun := g
      left_inv := hgf
      right_inv := hfg
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply Continuous.prodMk hπ
    apply Continuous.subtype_mk
    exact continuous_id.mul (s.continuous.comp hπ).inv
  · exact (continuous_subtype_val.comp continuous_snd).mul (s.continuous.comp continuous_fst)

/-- The section cocycle of left translation, valued in the actual kernel. -/
def quotientSectionCocycle (n : N) (q : Q) : π.ker :=
  ⟨n * s q * (s (π n * q))⁻¹, by simp [hs]⟩

/-- Conjugation on the kernel, expressed without selecting logarithms. -/
def quotientKernelConjugate (n : N) (i : π.ker) : π.ker :=
  ⟨n * i * n⁻¹, by
    have hi : π i = 1 := i.property
    simp [hi]⟩

omit [IsTopologicalGroup Q] in
theorem quotientSection_left_translation (n : N) (p : Q × π.ker) :
    quotientSectionHomeomorph π hπ s hs
      (n * (quotientSectionHomeomorph π hπ s hs).symm p) =
    (π n * p.1, quotientKernelConjugate π n p.2 * quotientSectionCocycle π s hs n p.1) := by
  have hp : π p.2 = 1 := p.2.property
  apply Prod.ext
  · simp [quotientSectionHomeomorph, hp, hs]
  · apply Subtype.ext
    change n * ((p.2 : N) * s p.1) * (s (π (n * ((p.2 : N) * s p.1))))⁻¹ =
      (n * p.2 * n⁻¹) * (n * s p.1 * (s (π n * p.1))⁻¹)
    simp only [map_mul, hp, hs, one_mul]
    group

theorem continuous_quotientSectionCocycle (n : N) :
    Continuous (quotientSectionCocycle π s hs n) := by
  exact ((continuous_const.mul s.continuous).mul
    (s.continuous.comp (continuous_const.mul continuous_id)).inv).subtype_mk _

end PolycyclicRecognition

end

end OAI
