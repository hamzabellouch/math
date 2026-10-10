import OAI.Analysis.Pureness.Tensor.SpatialPowersPolynomial
import OAI.Analysis.Pureness.Tensor.SpatialCenteredPolynomials
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter
open scoped TensorProduct Topology
local instance spatialPowersSmallAverageDecidableEq {Domain : Type*} : DecidableEq Domain :=
  Classical.decEq Domain
variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

lemma exists_initialFreeSubgroup_support (a : FreeGroup ℕ →₀ A) :
    ∃ m, ∀ g ∈ a.support, g ∈ initialFreeSubgroup m := by
  have h : ∀ᶠ m in atTop, ∀ g ∈ a.support, g ∈ initialFreeSubgroup m := by
    rw [Filter.eventually_all_finset]
    exact fun g _ => eventually_mem_initialFreeSubgroup g
  exact h.exists

private lemma exists_small_square_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℝ)⁻¹ * (2 * Real.sqrt n * C) < ε := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max 0 (2*C/ε))
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkn : k ≠ 0 := by exact_mod_cast hk0.ne'
  have hc : 2*C < ε*(k : ℝ) := by
    have h := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hk)
    simpa only [mul_comm] using h
  refine ⟨k^2, pow_ne_zero _ hkn, ?_⟩
  rw [Nat.cast_pow,Real.sqrt_sq hk0.le]
  have he : ((k : ℝ)^2)⁻¹*(2*(k : ℝ)*C) = (2*C)/(k : ℝ) := by
    field_simp [ne_of_gt hk0]
  rw [he]
  exact (div_lt_iff₀ hk0).mpr hc

private lemma exists_small_of_bound (f : ℕ → ℝ) (C ε : ℝ) (hε : 0 < ε)
    (hf : ∀ n, f n ≤ (n : ℝ)⁻¹ * (2 * Real.sqrt n * C)) :
    ∃ n : ℕ, n ≠ 0 ∧ f n < ε := by
  obtain ⟨n, hn, hbound⟩ := exists_small_square_bound C ε hε
  exact ⟨n, hn, (hf n).trans_lt hbound⟩

theorem exists_small_spatial_polynomial_average (a : FreeGroup ℕ →₀ A) (ha : a 1 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m n, n ≠ 0 ∧ ‖spatialFreeGroupAverage α m n
      (spatialGroupPolynomialMap (G := FreeGroup ℕ) α a)‖ < ε := by
  have hsupport : ∃ m : ℕ, ∀ g ∈ a.support, g ∈ initialFreeSubgroup m :=
    exists_initialFreeSubgroup_support (A := A) a
  obtain ⟨m, hm⟩ := hsupport
  refine ⟨m, ?_⟩
  exact exists_small_of_bound
    (fun n => ‖spatialFreeGroupAverage α m n
      (spatialGroupPolynomialMap (G := FreeGroup ℕ) α a)‖)
    ‖spatialGroupPolynomialMap (G := FreeGroup ℕ) α a‖ ε hε
    (fun n => spatialFreeGroupAverage_polynomial_bound α m n a ha hm)

private lemma norm_lt_of_half_bounds {V : Type*} [SeminormedAddCommGroup V]
    (x y : V) (ε : ℝ) (hxy : ‖x-y‖ < ε/2) (hy : ‖y‖ < ε/2) : ‖x‖ < ε := by
  have h := norm_add_le (x-y) y
  rw [sub_add_cancel] at h
  linarith

include hα in

theorem exists_small_spatial_centered_average
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
    (hx : spatialGroupFourier α (1 : FreeGroup ℕ) x = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ m n, n ≠ 0 ∧ ‖spatialFreeGroupAverage α m n x‖ < ε := by
  obtain ⟨a,ha,hd⟩ := exists_centered_spatial_polynomial (G := FreeGroup ℕ) α hα x hx (ε/2) (half_pos hε)
  obtain ⟨m,n,hn,hb⟩ := exists_small_spatial_polynomial_average α a ha (ε/2) (half_pos hε)
  refine ⟨m,n,hn,?_⟩
  let p := spatialGroupPolynomialMap (G := FreeGroup ℕ) α a
  have hs : ‖spatialFreeGroupAverage α m n x-spatialFreeGroupAverage α m n p‖ ≤ ‖x-p‖ :=
    (congrArg norm (unitaryAverage_sub
      (B := representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
      (fun i : Fin n => spatialGroupUnitary α (FreeGroup.of (m+i.val))) x p).symm).le.trans
      (unitaryAverage_norm_le _ _)
  exact norm_lt_of_half_bounds _ _ ε (hs.trans_lt hd) hb

end CuntzPureness

end

end OAI
