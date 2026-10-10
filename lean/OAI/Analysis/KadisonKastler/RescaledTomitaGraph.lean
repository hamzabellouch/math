import OAI.Analysis.KadisonKastler.PreparedPairState
import OAI.Analysis.FactorGeneration.Bicommutant
import Mathlib.Tactic.FinCases

namespace OAI

/-! # Rescaled Tomita graphs in a fixed two-coordinate Hilbert space

A fixed conjugation identifies the conjugate copy of the Hilbert space
with the original one. In these coordinates the graph vector is
`(x Ω, c J (x* Ω))`. The same identification is used for both algebras.
No closability or modular spectral theorem is needed for the closed
linear graph subspace or the elementary projection comparison below.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The fixed Hilbert space in which the two rescaled graphs are compared. -/
abbrev TomitaGraphHilbert (H : Type*) := Generator.FiniteHilbert (Fin 2) H

/-- Graph coordinates after identifying the conjugate Hilbert space by `J`. -/
def rescaledGraphVector (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (x : H →L[ℂ] H) : TomitaGraphHilbert H :=
  WithLp.toLp 2 ![x Ω, c • J (star x Ω)]

@[simp] theorem rescaledGraphVector_zero (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (x : H →L[ℂ] H) : rescaledGraphVector J Ω c x 0 = x Ω := rfl

@[simp] theorem rescaledGraphVector_one (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (x : H →L[ℂ] H) : rescaledGraphVector J Ω c x 1 = c • J (star x Ω) := rfl

/-- The conjugation in the second coordinate makes the graph map
complex-linear rather than conjugate-linear. -/
def rescaledGraphMap (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : Algebra P →ₗ[ℂ] TomitaGraphHilbert H where
  toFun x := rescaledGraphVector J Ω c x.val
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rescaledGraphVector, star_add, map_add, smul_add]
  map_smul' z x := by
    ext i
    fin_cases i
    · simp [rescaledGraphVector]
    · change c • J (star (z • x.val) Ω) = z • (c • J (star x.val Ω))
      rw [star_smul, smul_apply, J.map_smulₛₗ]
      change c • (star (star z) • J (star x.val Ω)) = z • (c • J (star x.val Ω))
      rw [star_star, smul_comm]

@[simp] theorem rescaledGraphMap_apply (P : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) (x : Algebra P) :
    rescaledGraphMap P J Ω c x = rescaledGraphVector J Ω c x.val := rfl

/-- The defining weighted graph norm, with no restriction on the scale. -/
theorem norm_rescaledGraphVector_sq (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c x‖ ^ 2 = ‖x Ω‖ ^ 2 + c ^ 2 * ‖star x Ω‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, rescaledGraphVector_zero, rescaledGraphVector_one,
    norm_smul, J.norm_map, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The closed linear rescaled graph. -/
def rescaledGraphSubspace (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : Submodule ℂ (TomitaGraphHilbert H) :=
  (rescaledGraphMap P J Ω c).range.topologicalClosure

instance rescaledGraphSubspace_complete (P : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    CompleteSpace (rescaledGraphSubspace P J Ω c) :=
  inferInstanceAs (CompleteSpace (rescaledGraphMap P J Ω c).range.topologicalClosure)

theorem rescaledGraphVector_mem (P : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) (x : Algebra P) :
    rescaledGraphVector J Ω c x.val ∈ rescaledGraphSubspace P J Ω c :=
  Submodule.le_topologicalClosure _ ⟨x, rfl⟩

/-- Orthogonal projection onto the closed graph. -/
def rescaledGraphProjection (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H :=
  (rescaledGraphSubspace P J Ω c).starProjection

theorem rescaledGraphProjection_vector (P : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) (x : Algebra P) :
    rescaledGraphProjection P J Ω c (rescaledGraphVector J Ω c x.val) =
      rescaledGraphVector J Ω c x.val :=
  (rescaledGraphSubspace P J Ω c).starProjection_eq_self_iff.mpr
    (rescaledGraphVector_mem P J Ω c x)

/-- A bound on the defining graph vectors extends to their actual closure. -/
theorem rescaledGraph_bound_on_closure
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (B : ℝ)
    (hB : ∀ x : Algebra P,
      ‖T (rescaledGraphVector J Ω c x.val)‖ ≤ B * ‖rescaledGraphVector J Ω c x.val‖)
    {ξ : TomitaGraphHilbert H} (hξ : ξ ∈ rescaledGraphSubspace P J Ω c) :
    ‖T ξ‖ ≤ B * ‖ξ‖ := by
  have hc : IsClosed {ξ : TomitaGraphHilbert H | ‖T ξ‖ ≤ B * ‖ξ‖} :=
    isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)
  exact closure_minimal (by rintro _ ⟨x, rfl⟩; exact hB x) hc hξ

/-- A graph-vector estimate bounds the operator after graph projection. -/
theorem norm_comp_rescaledGraphProjection_le
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ x : Algebra P,
      ‖T (rescaledGraphVector J Ω c x.val)‖ ≤ B * ‖rescaledGraphVector J Ω c x.val‖) :
    ‖T * rescaledGraphProjection P J Ω c‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro ξ
  change ‖T ((rescaledGraphSubspace P J Ω c).starProjection ξ)‖ ≤ B * ‖ξ‖
  exact (rescaledGraph_bound_on_closure P J Ω c T B hv
    ((rescaledGraphSubspace P J Ω c).starProjection_apply_mem ξ)).trans
    (mul_le_mul_of_nonneg_left
      ((rescaledGraphSubspace P J Ω c).norm_starProjection_apply_le ξ) hB)

private theorem norm_product_reverse_of_selfAdjoint {A : Type*}
    [NormedRing A] [StarRing A] [NormedStarGroup A]
    (x y : A) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : ‖x * y‖ = ‖y * x‖ := by
  calc
    _ = ‖star (x * y)‖ := (norm_star (x * y)).symm
    _ = _ := by rw [star_mul, hx.star_eq, hy.star_eq]

/-- Two directional graph-vector estimates give a uniform comparison
of the actual orthogonal graph projections. -/
theorem norm_rescaledGraphProjection_sub_le
    (P Q : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hPQ : ∀ x : Algebra P,
      ‖(1 - rescaledGraphProjection Q J Ω c) (rescaledGraphVector J Ω c x.val)‖ ≤
        B * ‖rescaledGraphVector J Ω c x.val‖)
    (hQP : ∀ x : Algebra Q,
      ‖(1 - rescaledGraphProjection P J Ω c) (rescaledGraphVector J Ω c x.val)‖ ≤
        B * ‖rescaledGraphVector J Ω c x.val‖) :
    ‖rescaledGraphProjection P J Ω c - rescaledGraphProjection Q J Ω c‖ ≤ 2 * B := by
  let EP : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H :=
    rescaledGraphProjection P J Ω c
  let EQ : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H :=
    rescaledGraphProjection Q J Ω c
  have h₁ : ‖(1 - EQ) * EP‖ ≤ B :=
    norm_comp_rescaledGraphProjection_le P J Ω c (1 - EQ) hB hPQ
  have h₂ : ‖(1 - EP) * EQ‖ ≤ B :=
    norm_comp_rescaledGraphProjection_le Q J Ω c (1 - EP) hB hQP
  have hEP : IsSelfAdjoint EP :=
    (isStarProjection_starProjection (U := rescaledGraphSubspace P J Ω c)).isSelfAdjoint
  have hEQ : IsSelfAdjoint EQ :=
    (isStarProjection_starProjection (U := rescaledGraphSubspace Q J Ω c)).isSelfAdjoint
  have hOne : IsSelfAdjoint (1 : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :=
    IsSelfAdjoint.one (TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
  have hrev : ‖EQ * (1 - EP)‖ = ‖(1 - EP) * EQ‖ :=
    norm_product_reverse_of_selfAdjoint EQ (1 - EP) hEQ (hOne.sub hEP)
  calc
    ‖EP - EQ‖ = ‖(1 - EQ) * EP - EQ * (1 - EP)‖ := by
      congr 1
      simp only [mul_sub, sub_mul, mul_one, one_mul]
      abel
    _ ≤ ‖(1 - EQ) * EP‖ + ‖EQ * (1 - EP)‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add h₁ (hrev.le.trans h₂)
    _ = 2 * B := by ring

end

end KadisonKastler

end OAI
