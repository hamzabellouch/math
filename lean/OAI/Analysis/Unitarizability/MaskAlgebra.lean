import OAI.Analysis.Unitarizability.Masked
import OAI.Analysis.Unitarizability.SparseMask

namespace OAI

/-! Sparse masks yield operator conjugation identities, and the
constant mask has a rank-one collision kernel. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
open scoped ComplexConjugate
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq ℂ := Classical.decEq ℂ

/-- The masked operator bound in finite-cardinality form. -/
theorem masked_bound_of_frame (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {p : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v p b)
    (hr : ∀ x, (rowSet c x).card ≤ p) (hcol : ∀ y, (columnSet s c y).card ≤ p) :
    ‖operator v s c hc‖ ≤ b^2 :=
  masked_bound v s c hc hb (fun x => hv _ (hr x)) (fun y => hv _ (hcol y))

theorem operator_sub (v : I → Fibre K) (s : I → G) (c d : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (hd : ∀ x i, ‖d x i‖ ≤ 1)
    (hcd : ∀ x i, ‖c x i - d x i‖ ≤ 1) :
    operator v s c hc - operator v s d hd = operator v s (fun x i => c x i-d x i) hcd := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change operator v s c hc ξ x - operator v s d hd ξ x = _
  simp only [operator_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

theorem conjugate_operator (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (g : G) :
    conjugate KernelObstruction.translation g (operator v s c hc) =
      operator v s (fun x i => c (g⁻¹*x) i) (fun _ i => hc _ i) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change KernelObstruction.translation g (operator v s c hc (KernelObstruction.translation g⁻¹ ξ)) x = _
  simp only [KernelObstruction.translation_apply, operator_apply, inv_inv,
    ← mul_assoc, mul_inv_cancel, one_mul]

def constant (v : I → Fibre K) (s : I → G) : Space G K →L[ℂ] Space G K :=
  operator v s (fun _ _ => 1) (fun _ _ => by simp)

theorem constant_commutant (v : I → Fibre K) (s : I → G) :
    constant v s ∈ KernelObstruction.Commutant := by
  intro g
  apply Commute.symm
  apply (conjugate_eq_self_iff_commute KernelObstruction.translation g (constant v s)).mp
  exact conjugate_operator v s (fun _ _ => 1) (fun _ _ => by simp) g

theorem basis_inner_right (v : Fibre K) (b : K) :
    inner ℂ v (EuclideanSpace.basisFun K ℂ b) = conj (v b) := by
  rw [← EuclideanSpace.basisFun_inner K ℂ v b, inner_conj_symm]

theorem constant_kernel (v : I → Fibre K) (s : I → G) (g : G) :
    KernelObstruction.coefficients (KernelObstruction.block (constant v s) 1 g) =
      kernelCoefficients v s g := by
  apply (WithLp.equiv 2 ((K × K) → ℂ)).injective
  funext ab
  rcases ab with ⟨a,b⟩
  change (constant v s (lp.single (E := fun _ : G => Fibre K) 2 g (EuclideanSpace.basisFun K ℂ b)) 1) a = kernelCoefficients v s g (a,b)
  simp only [constant, operator_apply, one_mul, kernelCoefficients,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : s i = g
  · simp only [h, lp.single_apply_self, ite_true]
    change inner ℂ (v i) (EuclideanSpace.basisFun K ℂ b) * v i a = v i a * conj (v i b)
    rw [basis_inner_right, mul_comm]
  · simp [h]

theorem constant_energy_ge_card (v : I → Fibre K) (hv : ∀ i, ‖v i‖ = 1) (s : I → G) :
    (Fintype.card I : ℝ) ≤ KernelObstruction.energy (constant v s) := by
  unfold KernelObstruction.energy
  simp_rw [constant_kernel]
  exact kernel_energy_ge_card v hv s

omit [Group G] [Fintype I] in
theorem bool_mask_norm (a : G → I → Bool) (x : G) (i : I) : ‖boolComplex (a x i)‖ ≤ 1 := by
  cases a x i <;> simp [boolComplex]

def oriented (v : I → Fibre K) (s : I → G) (a : G → I → Bool) : Space G K →L[ℂ] Space G K :=
  operator v s (fun x i => boolComplex (a x i)) (bool_mask_norm a)

theorem difference_operator (v : I → Fibre K) (s : I → G) (a : G → I → Bool) (g : G) :
    coboundary KernelObstruction.translation (oriented v s a) g =
      operator v s (fun x i => boolComplex (a x i) - boolComplex (a (g⁻¹*x) i))
        (fun _ _ => difference_mask_norm _ _) := by
  rw [coboundary, oriented, conjugate_operator]
  exact operator_sub _ _ _ _ _ _ _

theorem difference_norm_le (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (hc : ∀ y, (columnZeros a s y).card ≤ r) (g : G) :
    ‖coboundary KernelObstruction.translation (oriented v s a) g‖ ≤ b^2 := by
  rw [difference_operator]
  apply masked_bound_of_frame _ _ _ _ hb hv
  · intro x
    have h : rowSet (fun x i => boolComplex (a x i) - boolComplex (a (g⁻¹*x) i)) x = rowDifference a g x := by
      ext i
      simp [rowSet, rowDifference, difference_mask_ne_zero]
    rw [h]
    exact rowDifference_card_le a r hr g x
  · intro y
    have h : columnSet s (fun x i => boolComplex (a x i) - boolComplex (a (g⁻¹*x) i)) y = columnDifference a s g y := by
      ext i
      simp [columnSet, columnDifference, difference_mask_ne_zero]
    rw [h]
    exact columnDifference_card_le a s r hc g y

end Masked
end Dixmier

end

end OAI
