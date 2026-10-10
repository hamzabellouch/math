import OAI.Analysis.IrrationalRotation.Operators.TracialProjectionTransport
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Invariant233.ProjectionMeetTrace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorFunctional (ξ : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ H ξ)

omit [CompleteSpace H] in
@[simp] theorem vectorFunctional_apply (ξ : H) (A : H →L[ℂ] H) :
    vectorFunctional ξ A = vectorTrace ξ A := rfl

theorem norm_one_sub_gram_le_one (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) :
    ‖1 - star A * A‖ ≤ 1 := by
  have hgram : 0 ≤ star A * A := star_mul_self_nonneg A
  have hnorm : ‖star A * A‖ ≤ 1 := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg A]
  have hle : star A * A ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hgram).mp hnorm
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hle)).mpr
    (sub_le_self _ hgram)

omit [CompleteSpace H] in

theorem mul_complement_pow (a b : H →L[ℂ] H) (n : ℕ) :
    a * (1 - b * a) ^ n = (1 - a * b) ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    noncomm_ring

theorem vectorTrace_complement_pow_eq
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M) (n : ℕ) :
    vectorTrace ξ ((1 - a * b) ^ n) = vectorTrace ξ ((1 - b * a) ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : (1 - a * b) ^ n ∈ M := pow_mem (sub_mem (one_mem M) (mul_mem ha hb)) n
    have hcycle := htrace ((1 - a * b) ^ n * a) b (mul_mem hp ha) hb
    have hterm : vectorTrace ξ (((1 - a * b) ^ n * a) * b) =
        vectorTrace ξ (((1 - b * a) ^ n * b) * a) := by
      rw [hcycle, ← mul_assoc, mul_complement_pow b a n]
    simpa only [pow_succ, mul_sub, mul_one, ← mul_assoc,
      vectorTrace, sub_apply, inner_sub_right] using congrArg₂ (fun x y : ℂ => x - y) ih hterm

def meanOperator (A : H →L[ℂ] H) (n : ℕ) : H →L[ℂ] H :=
  (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, A ^ k

omit [CompleteSpace H] in

theorem meanOperator_apply (A : H →L[ℂ] H) (n : ℕ) (x : H) :
    meanOperator A n x = birkhoffAverage ℂ A id n x := by
  simp only [meanOperator, birkhoffAverage, birkhoffSum, smul_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact (congrArg (fun f : H →ₗ[ℂ] H => f x) (ContinuousLinearMap.toLinearMap_pow A k)).trans
    (congrFun (Module.End.coe_pow A.toLinearMap k) x)

theorem eqLocus_one_sub_gram (A : H →L[ℂ] H) :
    (1 - star A * A).eqLocus (1 : H →L[ℂ] H) = A.ker := by
  rw [← A.ker_adjoint_comp_self]
  ext x
  change x - (A.adjoint (A x)) = x ↔ A.adjoint (A x) = 0
  exact sub_eq_self

theorem meanOperator_one_sub_gram_tendsto (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) (x : H) :
    Tendsto (fun n => meanOperator (1 - star A * A) n x) atTop
      (𝓝 (A.ker.starProjection x)) := by
  have ht := (1 - star A * A).tendsto_birkhoffAverage_orthogonalProjection
    (norm_one_sub_gram_le_one A hA) x
  simp only [← meanOperator_apply] at ht
  change Tendsto (fun n => meanOperator (1 - star A * A) n x) atTop
    (𝓝 (((1 - star A * A).eqLocus (1 : H →L[ℂ] H)).starProjection x)) at ht
  simpa only [eqLocus_one_sub_gram] using ht

theorem vectorTrace_kernel_eq_adjoint_kernel
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (A : H →L[ℂ] H) (hA : A ∈ M) (hnorm : ‖A‖ ≤ 1) :
    vectorTrace ξ A.ker.starProjection = vectorTrace ξ A.adjoint.ker.starProjection := by
  have hnstar : ‖star A‖ ≤ 1 := by simpa using hnorm
  have hlim : Tendsto (fun n => vectorTrace ξ (meanOperator (1 - star A * A) n))
      atTop (𝓝 (vectorTrace ξ A.ker.starProjection)) :=
    tendsto_const_nhds.inner (meanOperator_one_sub_gram_tendsto A hnorm ξ)
  have hlimStar : Tendsto (fun n => vectorTrace ξ
      (meanOperator (1 - star (star A) * star A) n)) atTop
      (𝓝 (vectorTrace ξ (star A).ker.starProjection)) :=
    tendsto_const_nhds.inner (meanOperator_one_sub_gram_tendsto (star A) hnstar ξ)
  have heq : ∀ n, vectorTrace ξ (meanOperator (1 - star A * A) n) =
      vectorTrace ξ (meanOperator (1 - star (star A) * star A) n) := by
    intro n
    change vectorFunctional ξ (meanOperator (1 - star A * A) n) =
      vectorFunctional ξ (meanOperator (1 - star (star A) * star A) n)
    simp only [meanOperator, map_smul, map_sum, star_star]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact vectorTrace_complement_pow_eq M ξ htrace (star A) A (star_mem hA) hA k
  have hlim' : Tendsto (fun n => vectorTrace ξ
      (meanOperator (1 - star (star A) * star A) n)) atTop
      (𝓝 (vectorTrace ξ A.ker.starProjection)) := by
    convert hlim using 1
    funext n
    exact (heq n).symm
  have hresult := tendsto_nhds_unique hlim' hlimStar
  simpa only [vectorTrace, ContinuousLinearMap.star_eq_adjoint] using hresult

private instance inf_complete (p q : Submodule ℂ H) [CompleteSpace p] [CompleteSpace q] :
    CompleteSpace ↥(p ⊓ q) := by
  have hp : IsClosed (p : Set H) := (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  have hq : IsClosed (q : Set H) := (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  exact (hp.inter hq).completeSpace_coe

omit [CompleteSpace H] in

theorem projection_mul_of_le {p q : Submodule ℂ H}
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection] (h : p ≤ q) :
    q.starProjection * p.starProjection = p.starProjection := by
  ext x
  exact q.starProjection_eq_self_iff.mpr (h (p.starProjection_apply_mem x))

theorem kernel_projection_complement_mul (p q : Submodule ℂ H)
    [CompleteSpace p] [CompleteSpace q] :
    ((1 - q.starProjection) * p.starProjection).ker.starProjection =
      1 - p.starProjection + (p ⊓ q).starProjection := by
  let A := (1 - q.starProjection) * p.starProjection
  let R := (p ⊓ q).starProjection
  have hpR : p.starProjection * R = R := projection_mul_of_le inf_le_left
  have hRp : R * p.starProjection = R :=
    Submodule.starProjection_comp_starProjection_of_le inf_le_left
  have hqR : q.starProjection * R = R := projection_mul_of_le inf_le_right
  have horth : (1 - p.starProjection) * R = 0 := by
    rw [sub_mul, one_mul, hpR, sub_self]
  have hproj : IsStarProjection (1 - p.starProjection + R) :=
    isStarProjection_starProjection.one_sub.add isStarProjection_starProjection horth
  have hAp : A * (1 - p.starProjection + R) = 0 := by
    dsimp [A]
    have hpp := p.isIdempotentElem_starProjection.eq
    noncomm_ring [hpp, hpR, hqR]
  have hrange : (1 - p.starProjection + R).range = A.ker := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      change A ((1 - p.starProjection + R) x) = 0
      have hx := congrArg (fun B : H →L[ℂ] H => B x) hAp
      exact hx
    · intro x hx
      have hAx : p.starProjection x - q.starProjection (p.starProjection x) = 0 := hx
      have hpq : p.starProjection x ∈ p ⊓ q := by
        exact ⟨p.starProjection_apply_mem x,
          q.starProjection_eq_self_iff.mp (sub_eq_zero.mp hAx).symm⟩
      have hRx : R x = p.starProjection x := by
        have h1 : R (p.starProjection x) = p.starProjection x :=
          (p ⊓ q).starProjection_eq_self_iff.mpr hpq
        have h2 := congrArg (fun B : H →L[ℂ] H => B x) hRp
        exact h2.symm.trans h1
      refine ⟨x, ?_⟩
      change x - p.starProjection x + R x = x
      rw [hRx, sub_add_cancel]
  obtain ⟨hinst, heq⟩ := isStarProjection_iff_eq_starProjection_range.mp hproj
  simpa only [hrange] using heq.symm

theorem meet_projection_mem (M : VonNeumannAlgebra H) (p q : Submodule ℂ H)
    [CompleteSpace p] [CompleteSpace q]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M) :
    (p ⊓ q).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff isStarProjection_starProjection M).mpr
  intro W hW
  rw [Submodule.range_starProjection]
  have hpW := (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mp hp W hW
  have hqW := (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mp hq W hW
  rw [Submodule.range_starProjection] at hpW hqW
  intro x hx
  exact ⟨hpW hx.1, hqW hx.2⟩

omit [CompleteSpace H] in

theorem norm_projection_le_one (p : Submodule ℂ H) [p.HasOrthogonalProjection] :
    ‖p.starProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using p.norm_starProjection_apply_le x

theorem vectorTrace_meet_lower_bound
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (p q : Submodule ℂ H) [CompleteSpace p] [CompleteSpace q]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M) :
    (vectorTrace ξ p.starProjection).re + (vectorTrace ξ q.starProjection).re -
      ‖ξ‖ ^ 2 ≤ (vectorTrace ξ (p ⊓ q).starProjection).re := by
  let A := (1 - q.starProjection) * p.starProjection
  have hAmem : A ∈ M := mul_mem (sub_mem (one_mem M) hq) hp
  have hqn : ‖1 - q.starProjection‖ ≤ 1 := by
    have hh := norm_projection_le_one qᗮ
    simpa only [Submodule.starProjection_orthogonal, ContinuousLinearMap.one_def] using hh
  have hpn := norm_projection_le_one p
  have hAn : ‖A‖ ≤ 1 := by
    apply (norm_mul_le _ _).trans
    nlinarith [norm_nonneg (1 - q.starProjection), norm_nonneg p.starProjection]
  have hstar : A.adjoint = p.starProjection * (1 - q.starProjection) := by
    change star A = _
    simp only [A, star_mul, star_sub, star_one,
      (isSelfAdjoint_starProjection p).star_eq, (isSelfAdjoint_starProjection q).star_eq]
  have hqker : q ≤ A.adjoint.ker := by
    intro x hx
    change A.adjoint x = 0
    rw [hstar]
    change p.starProjection (x - q.starProjection x) = 0
    rw [q.starProjection_eq_self_iff.mpr hx, sub_self, map_zero]
  have hmono := TracialProjectionTransport.vectorTrace_projection_mono ξ hqker
  have hsame := vectorTrace_kernel_eq_adjoint_kernel M ξ htrace A hAmem hAn
  rw [← hsame] at hmono
  change (vectorTrace ξ q.starProjection).re ≤
    (vectorTrace ξ (((1 - q.starProjection) * p.starProjection).ker.starProjection)).re at hmono
  rw [kernel_projection_complement_mul] at hmono
  have hone : (vectorTrace ξ (1 : H →L[ℂ] H)).re = ‖ξ‖ ^ 2 := by
    exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ
  have hadd : vectorTrace ξ (1 - p.starProjection + (p ⊓ q).starProjection) =
      vectorTrace ξ 1 - vectorTrace ξ p.starProjection +
        vectorTrace ξ (p ⊓ q).starProjection := by
    simp only [vectorTrace, add_apply, sub_apply, inner_add_right, inner_sub_right]
  rw [hadd, Complex.add_re, Complex.sub_re, hone] at hmono
  linarith

theorem faithful_vectorTrace_meet_lower_bound
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (p q : Submodule ℂ H) [CompleteSpace p] [CompleteSpace q]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M) :
    (vectorTrace ξ p.starProjection).re + (vectorTrace ξ q.starProjection).re - 1 ≤
      (vectorTrace ξ (p ⊓ q).starProjection).re := by
  simpa only [hξ.1, one_pow] using vectorTrace_meet_lower_bound M ξ hξ.2.1 p q hp hq

end Invariant233.ProjectionMeetTrace

end

end OAI
