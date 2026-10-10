import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.TensorProductMatrices
import OAI.Probability.BinarySweep.Representations.IsotypicSpectral

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

lemma symmetric_projection_commutes (S : Submodule ℂ W) (A : Module.End ℂ W)
    (hA : A.IsSymmetric) (hS : ∀ w ∈ S, A w ∈ S) (w : W) :
    A (S.starProjection w) = S.starProjection (A w) := by
  symm
  apply S.eq_starProjection_of_mem_of_inner_eq_zero (hS _ (S.starProjection_apply_mem w))
  intro u hu
  rw [← map_sub, hA]
  exact S.starProjection_inner_eq_zero w (A u) (hS u hu)

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma isotypic_norm_cap [ρ.IsIrreducible] (B : Module.End ℂ W)
    (hT : ∀ g w, (B.adjoint * B) (σ g w) = σ g ((B.adjoint * B) w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (ht : (LinearMap.trace ℂ W (B.adjoint * B)).re = 1)
    {w : W} (hw : w ∈ isotypicSpan ρ σ) :
    (Module.finrank ℂ V : ℝ) * ‖B w‖^2 ≤ ‖w‖^2 := by
  have hp : (B.adjoint * B).IsPositive := LinearMap.isPositive_adjoint_comp_self B
  have hc := (isotypic_restriction_cap ρ σ (B.adjoint*B) hp hT hσ).2 ⟨w,hw⟩
  have hr := hc
  change 0 ≤ (inner ℂ ((↑((LinearMap.trace ℂ W) (B.adjoint*B)).re : ℂ) • w -
    (Module.finrank ℂ V : ℂ) • B.adjoint (B w)) w).re at hr
  rw [ht,Complex.ofReal_one,one_smul,inner_sub_left,inner_smul_left,
    LinearMap.adjoint_inner_left,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at hr
  simp only [← RCLike.ofReal_pow,Complex.sub_re,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,map_natCast,zero_mul,sub_zero] at hr
  change 0 ≤ ‖w‖^2 - (Module.finrank ℂ V : ℝ)*‖B w‖^2 at hr
  linarith

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem whitening_norm [ρ.IsIrreducible] (B A : Module.End ℂ W)
    (hA : A.IsSymmetric) (hAc : ∀ g w, A (σ g w) = σ g (A w))
    (hBA : B*A = 1)
    (hT : ∀ g w, (B.adjoint * B) (σ g w) = σ g ((B.adjoint * B) w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (ht : (LinearMap.trace ℂ W (B.adjoint * B)).re = 1) (w : W) :
    (Module.finrank ℂ V : ℝ) * ‖(isotypicSpan ρ σ).starProjection w‖^2 ≤ ‖A w‖^2 := by
  let S := isotypicSpan ρ σ
  have hi := commuting_isotypic_invariant ρ σ A hAc
  have hb : B (A (S.starProjection w)) = S.starProjection w := by
    exact congrArg (fun T : Module.End ℂ W => T (S.starProjection w)) hBA
  have hn := isotypic_norm_cap ρ σ B hT hσ ht
    (hi _ (S.starProjection_apply_mem w))
  rw [hb,symmetric_projection_commutes S A hA hi] at hn
  exact hn.trans (pow_le_pow_left₀ (norm_nonneg _) (S.norm_starProjection_apply_le (A w)) 2)

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem whitening_positive [ρ.IsIrreducible] (B A : Module.End ℂ W)
    (hA : A.IsSymmetric) (hAc : ∀ g w, A (σ g w) = σ g (A w))
    (hBA : B*A = 1)
    (hT : ∀ g w, (B.adjoint * B) (σ g w) = σ g ((B.adjoint * B) w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (ht : (LinearMap.trace ℂ W (B.adjoint * B)).re = 1) :
    (A.adjoint * A - (Module.finrank ℂ V : ℂ) •
      (isotypicSpan ρ σ).starProjection.toLinearMap).IsPositive := by
  have hsym := (LinearMap.isPositive_adjoint_comp_self A).1
  have hP : (isotypicSpan ρ σ).starProjection.toLinearMap.IsSymmetric :=
    fun u v => (isotypicSpan ρ σ).inner_starProjection_left_eq_right u v
  refine ⟨hsym.sub (hP.smul (by simp)),?_⟩
  intro w
  have hn := whitening_norm ρ σ B A hA hAc hBA hT hσ ht w
  change 0 ≤ (inner ℂ (A.adjoint (A w) -
    (Module.finrank ℂ V : ℂ) • (isotypicSpan ρ σ).starProjection w) w).re
  rw [inner_sub_left,inner_smul_left,LinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K]
  simp only [Complex.sub_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    ← RCLike.ofReal_pow,map_natCast,zero_mul,sub_zero]
  change 0 ≤ ‖A w‖^2 - (Module.finrank ℂ V : ℝ) *
    RCLike.re (inner ℂ ((isotypicSpan ρ σ).starProjection w) w)
  rw [(isotypicSpan ρ σ).re_inner_starProjection_eq_normSq]
  exact sub_nonneg.mpr hn

end BinaryCoordinateSweeps.Irrep

end

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma trace_product_nonneg {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A*B).trace := by
  obtain ⟨X,hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hX,Matrix.star_eq_conjTranspose,Matrix.trace_mul_cycle,Matrix.trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same X).trace_nonneg

lemma trace_product_mono {A B C : Matrix I I ℂ}
    (hA : A.PosSemidef) (hBC : (C-B).PosSemidef) : (A*B).trace ≤ (A*C).trace := by
  have h := trace_product_nonneg hA hBC
  rw [Matrix.mul_sub,Matrix.trace_sub] at h
  exact sub_nonneg.mp h

lemma trace_product_re_nonneg {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A*B).trace.re :=
  (Complex.nonneg_iff.mp (trace_product_nonneg hA hB)).1

lemma trace_product_re_mono {A B C : Matrix I I ℂ}
    (hA : A.PosSemidef) (hBC : (C-B).PosSemidef) :
    (A*B).trace.re ≤ (A*C).trace.re :=
  (Complex.le_def.mp (trace_product_mono hA hBC)).1

lemma tensor_product_trace_re {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] (R C : J → Matrix A A ℂ)
    (hR : ∀ j, (R j).PosSemidef) (hC : ∀ j, (C j).PosSemidef) :
    (tensorMatrices R * tensorMatrices C).trace.re = ∏ j, (R j * C j).trace.re := by
  rw [tensorMatrices_mul,tensorMatrices_trace]
  have hh (j : J) : (R j * C j).trace = ((R j * C j).trace.re : ℂ) := by
    apply Complex.ext <;> simp [ (Complex.nonneg_iff.mp (trace_product_nonneg (hR j) (hC j))).2]
  rw [show (∏ j, (R j * C j).trace) = ∏ j, ((R j * C j).trace.re : ℂ) from
    Finset.prod_congr rfl (fun j _ => hh j)]
  rw [← Complex.ofReal_prod,Complex.ofReal_re]

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

def parityProjection (p : A → Bool) : Matrix A A ℂ :=
  Matrix.diagonal (fun a => if p a then 1 else 0)

lemma commutes_parity_iff (p : A → Bool) (M : Matrix A A ℂ) :
    Commute M (parityProjection p) ↔ ∀ a b, p a ≠ p b → M a b = 0 := by
  constructor
  · intro h a b hab
    have he := congrArg (fun N : Matrix A A ℂ => N a b) h.eq
    simp only [parityProjection,Matrix.mul_diagonal,Matrix.diagonal_mul] at he
    cases ha : p a <;> cases hb : p b <;> simp_all
  · intro h
    apply Matrix.ext
    intro a b
    simp only [parityProjection,Matrix.mul_diagonal,Matrix.diagonal_mul]
    by_cases he : p a = p b
    · rw [he]; ring
    · rw [h a b he]; simp

lemma sqrt_commutes {M N : Matrix A A ℂ} (hM : M.PosSemidef) (hc : Commute M N) :
    Commute (CFC.sqrt M) N := by
  rw [CFC.sqrt_eq_real_sqrt M hM.nonneg]
  exact hc.cfcₙ (by rwa [hM.isHermitian.star_eq]) Real.sqrt

theorem exists_even_whitening (p : A → Bool) (M : Matrix A A ℂ)
    (hM : M.PosDef) (he : ∀ a b, p a ≠ p b → M a b = 0) :
    ∃ B C : Matrix A A ℂ,
      B.PosSemidef ∧ C.PosSemidef ∧ B*B = M ∧ B*C = 1 ∧ C*B = 1 ∧
      (∀ a b, p a ≠ p b → B a b = 0) ∧ (∀ a b, p a ≠ p b → C a b = 0) := by
  let B := CFC.sqrt M
  have hB : B.PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have hBB : B*B = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hu : IsUnit B := (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  let := hu.nonempty_invertible.some
  have heB := sqrt_commutes hM.posSemidef ((commutes_parity_iff p M).mpr he)
  refine ⟨B,⅟B,hB,?_,hBB,mul_invOf_self B,invOf_mul_self B,
    (commutes_parity_iff p B).mp heB,(commutes_parity_iff p (⅟B)).mp heB.invOf_left⟩
  rw [Matrix.invOf_eq_nonsing_inv]
  exact hB.inv

end BinaryCoordinateSweeps.Density

end

end OAI
