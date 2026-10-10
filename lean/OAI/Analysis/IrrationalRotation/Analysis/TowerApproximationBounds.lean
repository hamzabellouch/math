import OAI.Analysis.IrrationalRotation.Analysis.SeparatingVectorStrongConvergence
import OAI.Analysis.IrrationalRotation.Rotation.ProjectionDiagonal

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.TowerApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in

theorem sub_eq_mul_one_sub {A B P : H →L[ℂ] H} (h : A * P = B * P) :
    A - B = (A - B) * (1 - P) := by
  rw [mul_sub, mul_one, sub_mul, h, sub_self, sub_zero]

omit [CompleteSpace H] in

theorem norm_sub_apply_le {A B P : H →L[ℂ] H} (h : A * P = B * P) (ξ : H) :
    ‖A ξ - B ξ‖ ≤ (‖A‖ + ‖B‖) * ‖(1 - P) ξ‖ := by
  calc
    ‖A ξ - B ξ‖ = ‖(A - B) ((1 - P) ξ)‖ := by
      change ‖(A - B) ξ‖ = _
      conv_lhs => rw [sub_eq_mul_one_sub h]
      rfl
    _ ≤ ‖A - B‖ * ‖(1 - P) ξ‖ := (A - B).le_opNorm _
    _ ≤ (‖A‖ + ‖B‖) * ‖(1 - P) ξ‖ :=
      mul_le_mul_of_nonneg_right (norm_sub_le A B) (norm_nonneg _)

omit [CompleteSpace H] in

theorem norm_sub_apply_le_two_mul {A B P : H →L[ℂ] H}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (h : A * P = B * P) (ξ : H) :
    ‖A ξ - B ξ‖ ≤ 2 * ‖(1 - P) ξ‖ := by
  exact (norm_sub_apply_le h ξ).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

theorem vectorTrace_projection_re (P : H →L[ℂ] H) (hP : IsStarProjection P) (ξ : H) :
    (vectorTrace ξ P).re = ‖P ξ‖ ^ 2 := by
  change (inner ℂ ξ (P ξ)).re = _
  calc
    (inner ℂ ξ (P ξ)).re = (inner ℂ (P ξ) ξ).re :=
      inner_re_symm (𝕜 := ℂ) ξ (P ξ)
    _ = (inner ℂ (P ξ) (P ξ)).re := by
      rw [ProjectionDiagonal.inner_projection_eq_inner_projected P hP ξ]
    _ = ‖P ξ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem norm_sub_apply_sq_le_four_trace_compl {A B P : H →L[ℂ] H}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hP : IsStarProjection P)
    (h : A * P = B * P) (ξ : H) :
    ‖A ξ - B ξ‖ ^ 2 ≤ 4 * (vectorTrace ξ (1 - P)).re := by
  rw [vectorTrace_projection_re (1 - P) hP.one_sub ξ]
  have hnorm := norm_sub_apply_le_two_mul hA hB h ξ
  have hs := (sq_le_sq₀ (norm_nonneg (A ξ - B ξ))
    (show 0 ≤ 2 * ‖(1 - P) ξ‖ by positivity)).mpr hnorm
  nlinarith

theorem tendsto_apply_of_complement_trace_tendsto_zero
    {ι : Type*} {l : Filter ι} {A : ι → H →L[ℂ] H} {B : H →L[ℂ] H}
    {P : ι → H →L[ℂ] H} (ξ : H)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hP : ∀ i, IsStarProjection (P i)) (hagree : ∀ i, A i * P i = B * P i)
    (htrace : Tendsto (fun i => (vectorTrace ξ (1 - P i)).re) l (𝓝 0)) :
    Tendsto (fun i => A i ξ) l (𝓝 (B ξ)) := by
  have hnorm : Tendsto (fun i => ‖(1 - P i) ξ‖) l (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp htrace
    change Tendsto (fun i => Real.sqrt ((vectorTrace ξ (1 - P i)).re)) l
      (𝓝 (Real.sqrt 0)) at hsqrt
    simpa only [ vectorTrace_projection_re _ (hP _).one_sub ξ,
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun i => norm_sub_apply_le_two_mul (hA i) hB (hagree i) ξ)
    (by simpa using hnorm.const_mul 2)

theorem strong_tendsto_of_complement_trace_tendsto_zero
    {ι : Type*} {l : Filter ι} {M : VonNeumannAlgebra H} {ξ : H}
    (hfaithful : IsFaithfulTracialVector M ξ)
    {A : ι → H →L[ℂ] H} {B : H →L[ℂ] H} {P : ι → H →L[ℂ] H}
    (hAmem : ∀ i, A i ∈ M) (hBmem : B ∈ M)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hP : ∀ i, IsStarProjection (P i)) (hagree : ∀ i, A i * P i = B * P i)
    (htrace : Tendsto (fun i => (vectorTrace ξ (1 - P i)).re) l (𝓝 0)) (v : H) :
    Tendsto (fun i => A i v) l (𝓝 (B v)) :=
  hfaithful.strong_tendsto_of_bounded hAmem hBmem
    (tendsto_apply_of_complement_trace_tendsto_zero ξ hA hB hP hagree htrace)
    (Filter.Eventually.of_forall hA) v

end Invariant233.TowerApproximation

end

end OAI
