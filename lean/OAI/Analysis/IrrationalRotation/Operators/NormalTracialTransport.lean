import OAI.Analysis.IrrationalRotation.Model.NormalAffiliation
import OAI.Analysis.IrrationalRotation.Operators.BoundedRangeTrace
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Invariant233.NormalTracialTransport

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def extendedTrace (M : VonNeumannAlgebra H) (τ : TracialState M) :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  Classical.choose (exists_extension_norm_eq M.toSubalgebra.toSubmodule
    τ.toContinuousLinearMap)

theorem extendedTrace_apply (M : VonNeumannAlgebra H) (τ : TracialState M)
    (A : H →L[ℂ] H) (hA : A ∈ M) :
    extendedTrace M τ A = τ ⟨A, hA⟩ :=
  (Classical.choose_spec (exists_extension_norm_eq M.toSubalgebra.toSubmodule
    τ.toContinuousLinearMap)).1 ⟨A, hA⟩

@[simp] theorem extendedTrace_one (M : VonNeumannAlgebra H) (τ : TracialState M) :
    extendedTrace M τ 1 = 1 := by
  rw [extendedTrace_apply M τ 1 (one_mem M)]
  exact τ.map_one

theorem extendedTrace_cyclic (M : VonNeumannAlgebra H) (τ : TracialState M)
    (A B : H →L[ℂ] H) (hA : A ∈ M) (hB : B ∈ M) :
    extendedTrace M τ (A * B) = extendedTrace M τ (B * A) := by
  rw [extendedTrace_apply M τ _ (mul_mem hA hB),
    extendedTrace_apply M τ _ (mul_mem hB hA)]
  exact τ.tracial ⟨A, hA⟩ ⟨B, hB⟩

theorem extendedTrace_star (M : VonNeumannAlgebra H) (τ : TracialState M)
    (A : H →L[ℂ] H) (hA : A ∈ M) :
    extendedTrace M τ (star A) = star (extendedTrace M τ A) := by
  rw [extendedTrace_apply M τ _ (star_mem hA), extendedTrace_apply M τ A hA]
  exact τ.map_star ⟨A, hA⟩

theorem extendedTrace_projection_nonneg (M : VonNeumannAlgebra H) (τ : TracialState M)
    (P : H →L[ℂ] H) (hP : P ∈ M) (hp : IsStarProjection P) :
    0 ≤ (extendedTrace M τ P).re := by
  have hh := τ.positive (⟨P, hP⟩ : M)
  have hid : star P * P = P := by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  have heq : (star (⟨P, hP⟩ : M) * ⟨P, hP⟩ : M) = ⟨P, hP⟩ := Subtype.ext hid
  rw [heq] at hh
  rwa [extendedTrace_apply M τ P hP]

theorem extendedTrace_projection_real (M : VonNeumannAlgebra H) (τ : TracialState M)
    (P : H →L[ℂ] H) (hP : P ∈ M) (hp : IsStarProjection P) :
    ((extendedTrace M τ P).re : ℂ) = extendedTrace M τ P := by
  have hs := extendedTrace_star M τ P hP
  rw [hp.isSelfAdjoint.star_eq] at hs
  exact Complex.conj_eq_iff_re.mp hs.symm

theorem extendedTrace_tendsto (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    {ι : Type u} {L : Filter ι} [L.NeBot]
    (A : ι → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hA : ∀ i, A i ∈ M) (hB : B ∈ M)
    (hbound : ∃ C : ℝ, ∀ i, ‖A i‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun i => A i x) L (𝓝 (B x))) :
    Tendsto (fun i => extendedTrace M τ (A i)) L (𝓝 (extendedTrace M τ B)) := by
  have hh := hτ.2 ι L inferInstance (fun i => ⟨A i, hA i⟩) ⟨B, hB⟩ hbound hstrong
  simpa only [extendedTrace_apply M τ B hB,
    extendedTrace_apply M τ _ (hA _)] using hh

theorem extendedTrace_projection_mono (M : VonNeumannAlgebra H) (τ : TracialState M)
    (p q : Submodule ℂ H) [p.HasOrthogonalProjection] [q.HasOrthogonalProjection]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M) (hpq : p ≤ q) :
    (extendedTrace M τ p.starProjection).re ≤ (extendedTrace M τ q.starProjection).re := by
  have hproj : IsStarProjection (q.starProjection - p.starProjection) :=
    isStarProjection_starProjection.sub_of_mul_eq_left isStarProjection_starProjection
      (Submodule.starProjection_comp_starProjection_of_le hpq)
  have hnonneg := extendedTrace_projection_nonneg M τ _ (sub_mem hq hp) hproj
  rw [map_sub, Complex.sub_re] at hnonneg
  linarith

@[simp] theorem extendedTrace_orthogonal (M : VonNeumannAlgebra H) (τ : TracialState M)
    (p : Submodule ℂ H) [p.HasOrthogonalProjection] :
    extendedTrace M τ pᗮ.starProjection = 1 - extendedTrace M τ p.starProjection := by
  rw [Submodule.starProjection_orthogonal, ← ContinuousLinearMap.one_def, map_sub,
    extendedTrace_one]

open ProjectionMeetTrace BoundedRangeTrace

theorem extendedTrace_complement_pow_eq (M : VonNeumannAlgebra H) (τ : TracialState M)
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M) (n : ℕ) :
    extendedTrace M τ ((1 - a * b) ^ n) = extendedTrace M τ ((1 - b * a) ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : (1 - a * b) ^ n ∈ M := pow_mem (sub_mem (one_mem M) (mul_mem ha hb)) n
    have hcycle := extendedTrace_cyclic M τ ((1 - a * b) ^ n * a) b (mul_mem hp ha) hb
    have hterm : extendedTrace M τ (((1 - a * b) ^ n * a) * b) =
        extendedTrace M τ (((1 - b * a) ^ n * b) * a) := by
      rw [hcycle, ← mul_assoc, mul_complement_pow b a n]
    simpa only [pow_succ, mul_sub, mul_one, ← mul_assoc, map_sub] using
      congrArg₂ (fun x y : ℂ => x - y) ih hterm

theorem meanOperator_mem (M : VonNeumannAlgebra H) (A : H →L[ℂ] H)
    (hA : A ∈ M) (n : ℕ) : meanOperator A n ∈ M := by
  exact M.toSubalgebra.smul_mem (sum_mem fun k hk => pow_mem hA k) _

theorem norm_meanOperator_le_one (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) (n : ℕ) :
    ‖meanOperator A n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [meanOperator]
  have hpow : ∀ k : ℕ, ‖A ^ k‖ ≤ 1 := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero]
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simp
    | succ k ih =>
      rw [pow_succ]
      calc
        ‖A ^ k * A‖ ≤ ‖A ^ k‖ * ‖A‖ := norm_mul_le _ _
        _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg _)
        _ ≤ 1 := by simpa only [one_mul] using hA
  have hsum : ‖∑ k ∈ Finset.range n, A ^ k‖ ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := norm_sum_le_of_le _ (fun k hk => hpow k)
      _ = _ := by simp
  rw [meanOperator, norm_smul]
  apply (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)).trans
  simp [norm_inv, hn]

theorem extendedTrace_tendsto_nat (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hA : ∀ n, A n ∈ M) (hB : B ∈ M)
    (hbound : ∃ C : ℝ, ∀ n, ‖A n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (B x))) :
    Tendsto (fun n => extendedTrace M τ (A n)) atTop (𝓝 (extendedTrace M τ B)) := by
  let L : Filter (ULift.{u} ℕ) := Filter.map ULift.up atTop
  have hs : ∀ x, Tendsto (fun n : ULift.{u} ℕ => A n.down x) L (𝓝 (B x)) := by
    intro x
    change Filter.map (fun n : ULift.{u} ℕ => A n.down x)
      (Filter.map ULift.up atTop) ≤ _
    rw [Filter.map_map]
    exact hstrong x
  have ht := extendedTrace_tendsto M τ hτ (L := L)
    (fun n : ULift.{u} ℕ => A n.down) B (fun n => hA n.down) hB
    (by obtain ⟨C, hC⟩ := hbound; exact ⟨C, fun n => hC n.down⟩) hs
  exact ht.comp Filter.tendsto_map

theorem extendedTrace_kernel_eq_adjoint_kernel_of_norm_le_one
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (A : H →L[ℂ] H) (hA : A ∈ M) (hnorm : ‖A‖ ≤ 1) :
    extendedTrace M τ A.ker.starProjection =
      extendedTrace M τ A.adjoint.ker.starProjection := by
  have hnstar : ‖star A‖ ≤ 1 := by simpa using hnorm
  have hlim := extendedTrace_tendsto_nat M τ hτ
    (fun n => meanOperator (1 - star A * A) n) A.ker.starProjection
    (fun n => meanOperator_mem M _ (sub_mem (one_mem M) (mul_mem (star_mem hA) hA)) n)
    (kernel_projection_mem M A hA)
    ⟨1, fun n => norm_meanOperator_le_one _ (norm_one_sub_gram_le_one A hnorm) n⟩
    (meanOperator_one_sub_gram_tendsto A hnorm)
  have hlimStar := extendedTrace_tendsto_nat M τ hτ
    (fun n => meanOperator (1 - star (star A) * star A) n) (star A).ker.starProjection
    (fun n => meanOperator_mem M _
      (sub_mem (one_mem M) (mul_mem (star_mem (star_mem hA)) (star_mem hA))) n)
    (kernel_projection_mem M (star A) (star_mem hA))
    ⟨1, fun n => norm_meanOperator_le_one _
      (norm_one_sub_gram_le_one (star A) hnstar) n⟩
    (meanOperator_one_sub_gram_tendsto (star A) hnstar)
  have heq : ∀ n, extendedTrace M τ (meanOperator (1 - star A * A) n) =
      extendedTrace M τ (meanOperator (1 - star (star A) * star A) n) := by
    intro n
    simp only [meanOperator, map_smul, map_sum, star_star]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact extendedTrace_complement_pow_eq M τ (star A) A (star_mem hA) hA k
  have hlim' : Tendsto (fun n => extendedTrace M τ
      (meanOperator (1 - star (star A) * star A) n)) atTop
      (𝓝 (extendedTrace M τ A.ker.starProjection)) := by
    convert hlim using 1
    funext n
    exact (heq n).symm
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    tendsto_nhds_unique hlim' hlimStar

theorem extendedTrace_kernel_eq_adjoint_kernel
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (A : H →L[ℂ] H) (hA : A ∈ M) :
    extendedTrace M τ A.ker.starProjection =
      extendedTrace M τ A.adjoint.ker.starProjection := by
  let c : ℂ := ((1 + ‖A‖)⁻¹ : ℝ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero (by positivity))
  have hn : ‖c • A‖ ≤ 1 := by
    rw [norm_smul]
    have hcNorm : ‖c‖ = (1 + ‖A‖)⁻¹ := by
      simp only [c, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    rw [hcNorm]
    have hpos : 0 < 1 + ‖A‖ := by positivity
    rw [inv_mul_le_iff₀ hpos]
    linarith [norm_nonneg A]
  have heq := extendedTrace_kernel_eq_adjoint_kernel_of_norm_le_one M τ hτ
    (c • A) (M.toStarSubalgebra.smul_mem hA c) hn
  have hk : (c • A).ker = A.ker := by
    ext x
    change c • A x = 0 ↔ A x = 0
    simp only [smul_eq_zero, hc, false_or]
  have hka : (c • A).adjoint.ker = A.adjoint.ker := by
    rw [map_smulₛₗ]
    ext x
    change star c • A.adjoint x = 0 ↔ A.adjoint x = 0
    simp only [smul_eq_zero, star_ne_zero.mpr hc, false_or]
  simpa only [hk, hka] using heq

theorem range_closure_projection_mem (M : VonNeumannAlgebra H)
    (A : H →L[ℂ] H) (hA : A ∈ M) :
    A.range.topologicalClosure.starProjection ∈ M := by
  simpa only [range_closure_eq, Submodule.starProjection_orthogonal,
    ← ContinuousLinearMap.one_def] using
    (sub_mem (one_mem M) (kernel_projection_mem M A.adjoint (star_mem hA)))

theorem extendedTrace_range_eq_of_injective
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (A : H →L[ℂ] H) (hA : A ∈ M) (hinj : Function.Injective A)
    (p : Submodule ℂ H) [CompleteSpace p] (hp : p.starProjection ∈ M) :
    extendedTrace M τ (A * p.starProjection).range.topologicalClosure.starProjection =
      extendedTrace M τ p.starProjection := by
  have hk : (A * p.starProjection).ker = pᗮ := by
    rw [← p.ker_starProjection]
    ext x
    change A (p.starProjection x) = 0 ↔ p.starProjection x = 0
    exact map_eq_zero_iff A hinj
  have ht := extendedTrace_kernel_eq_adjoint_kernel M τ hτ
    (A * p.starProjection) (mul_mem hA hp)
  simp only [hk] at ht
  simp only [range_closure_eq, extendedTrace_orthogonal, ← ht]
  ring

theorem extendedTrace_preimage_eq
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (A : H →L[ℂ] H) (hA : A ∈ M) (hinj : Function.Injective A.adjoint)
    (p : Submodule ℂ H) [CompleteSpace p] (hp : p.starProjection ∈ M) :
    extendedTrace M τ ((1 - p.starProjection) * A).ker.starProjection =
      extendedTrace M τ p.starProjection := by
  have hstar : ((1 - p.starProjection) * A).adjoint =
      A.adjoint * (1 - p.starProjection) := by
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_sub, star_one,
      isStarProjection_starProjection.isSelfAdjoint.star_eq]
  have hk : ((1 - p.starProjection) * A).adjoint.ker = p := by
    rw [hstar]
    ext x
    change A.adjoint (x - p.starProjection x) = 0 ↔ x ∈ p
    rw [map_eq_zero_iff A.adjoint hinj, sub_eq_zero, eq_comm]
    exact p.starProjection_eq_self_iff
  have ht := extendedTrace_kernel_eq_adjoint_kernel M τ hτ
    ((1 - p.starProjection) * A) (mul_mem (sub_mem (one_mem M) hp) hA)
  simpa only [hk] using ht

theorem extendedTrace_le_of_normalizer
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (T : H →ₗ.[ℂ] H) (A B : H →L[ℂ] H)
    (hA : A ∈ M) (hB : B ∈ M)
    (hAinj : Function.Injective A.adjoint) (hBinj : Function.Injective B)
    (hD : ∀ x, A x ∈ T.domain) (hTA : ∀ x, T ⟨A x, hD x⟩ = B x)
    (p q : Submodule ℂ H) [CompleteSpace p] [CompleteSpace q]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M)
    (himage : InvariantRotation.AffiliatedTransport.transported T p ≤ q) :
    (extendedTrace M τ p.starProjection).re ≤
      (extendedTrace M τ q.starProjection).re := by
  let r := ((1 - p.starProjection) * A).ker
  have hr : r.starProjection ∈ M := kernel_projection_mem M _
    (mul_mem (sub_mem (one_mem M) hp) hA)
  have hrt : extendedTrace M τ r.starProjection = extendedTrace M τ p.starProjection :=
    extendedTrace_preimage_eq M τ hτ A hA hAinj p hp
  have hBt := extendedTrace_range_eq_of_injective M τ hτ B hB hBinj r hr
  have hle : (B * r.starProjection).range.topologicalClosure ≤
      InvariantRotation.AffiliatedTransport.transported T p := by
    apply Submodule.topologicalClosure_minimal _ _
      (Submodule.isClosed_topologicalClosure _)
    rintro y ⟨x, rfl⟩
    apply (InvariantRotation.AffiliatedTransport.domainImage T p).le_topologicalClosure
    apply InvariantRotation.AffiliatedTransport.mem_domainImage.mpr
    refine ⟨⟨A (r.starProjection x), hD _⟩, ?_, hTA _⟩
    have hm := r.starProjection_apply_mem x
    change A (r.starProjection x) - p.starProjection (A (r.starProjection x)) = 0 at hm
    exact p.starProjection_eq_self_iff.mp (sub_eq_zero.mp hm).symm
  have ht := extendedTrace_projection_mono M τ
    (B * r.starProjection).range.topologicalClosure q
    (range_closure_projection_mem M _ (mul_mem hB hr)) hq (hle.trans himage)
  simpa only [hBt, hrt] using ht

theorem extendedTrace_transported_eq_of_normalizer
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (T : H →ₗ.[ℂ] H) (hT : T.IsFormalAdjoint T) (hker : T.toFun.ker = ⊥)
    (A B : H →L[ℂ] H) (hA : A ∈ M) (hB : B ∈ M)
    (hAinj : Function.Injective A) (hAadj : Function.Injective A.adjoint)
    (hBinj : Function.Injective B) (hBadj : Function.Injective B.adjoint)
    (hD : ∀ x, A x ∈ T.domain) (hTA : ∀ x, T ⟨A x, hD x⟩ = B x)
    (p : Submodule ℂ H) [CompleteSpace p] (hp : p.starProjection ∈ M)
    (hP : (InvariantRotation.AffiliatedTransport.transported T p).starProjection ∈ M) :
    extendedTrace M τ (InvariantRotation.AffiliatedTransport.transported T p).starProjection =
      extendedTrace M τ p.starProjection := by
  let : CompleteSpace (InvariantRotation.AffiliatedTransport.transported T p) := by
    unfold InvariantRotation.AffiliatedTransport.transported
    infer_instance
  have hforward := extendedTrace_le_of_normalizer M τ hτ T A B hA hB
    hAadj hBinj hD hTA p (InvariantRotation.AffiliatedTransport.transported T p)
    hp hP le_rfl
  have hDinv : ∀ x, B x ∈ T.inverse.domain := by
    intro x
    rw [LinearPMap.inverse_domain]
    exact ⟨⟨A x, hD x⟩, hTA x⟩
  have hTinv : ∀ x, T.inverse ⟨B x, hDinv x⟩ = A x := by
    intro x
    have hpartialker : T.ker = ⊥ := by simp [LinearPMap.ker, hker]
    exact LinearPMap.inverse_apply_eq (x := ⟨A x, hD x⟩) (y := ⟨B x, hDinv x⟩)
      hpartialker (hTA x)
  have hpperp : pᗮ.starProjection ∈ M := by
    simpa only [Submodule.starProjection_orthogonal, ← ContinuousLinearMap.one_def] using
      (sub_mem (one_mem M) hp : (1 : H →L[ℂ] H) - p.starProjection ∈ M)
  have hPperp : (InvariantRotation.AffiliatedTransport.transported T p)ᗮ.starProjection ∈ M := by
    simpa only [Submodule.starProjection_orthogonal, ← ContinuousLinearMap.one_def] using
      (sub_mem (one_mem M) hP : (1 : H →L[ℂ] H) -
        (InvariantRotation.AffiliatedTransport.transported T p).starProjection ∈ M)
  have hback := extendedTrace_le_of_normalizer M τ hτ T.inverse B A hB hA
    hBadj hAinj hDinv hTinv pᗮ
    (InvariantRotation.AffiliatedTransport.transported T p)ᗮ hpperp hPperp
    (InvariantRotation.AffiliatedTransport.inverse_transported_le_orthogonal T p hT hker)
  rw [extendedTrace_orthogonal, extendedTrace_orthogonal] at hback
  have hre : (extendedTrace M τ (InvariantRotation.AffiliatedTransport.transported T p).starProjection).re =
      (extendedTrace M τ p.starProjection).re := by
    simp only [Complex.sub_re, Complex.one_re] at hback
    linarith
  rw [← extendedTrace_projection_real M τ _ hP isStarProjection_starProjection,
    ← extendedTrace_projection_real M τ _ hp isStarProjection_starProjection]
  exact congrArg Complex.ofReal hre

theorem transported_trace_eq_of_normalizer
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (T : H →ₗ.[ℂ] H) (hT : T.IsFormalAdjoint T) (hker : T.toFun.ker = ⊥)
    (A B : H →L[ℂ] H) (hA : A ∈ M) (hB : B ∈ M)
    (hAinj : Function.Injective A) (hAadj : Function.Injective A.adjoint)
    (hBinj : Function.Injective B) (hBadj : Function.Injective B.adjoint)
    (hD : ∀ x, A x ∈ T.domain) (hTA : ∀ x, T ⟨A x, hD x⟩ = B x)
    (p : Submodule ℂ H) [CompleteSpace p] (hp : p.starProjection ∈ M)
    (hP : (InvariantRotation.AffiliatedTransport.transported T p).starProjection ∈ M) :
    τ ⟨(InvariantRotation.AffiliatedTransport.transported T p).starProjection, hP⟩ =
      τ ⟨p.starProjection, hp⟩ := by
  simpa only [extendedTrace_apply M τ _ hP, extendedTrace_apply M τ _ hp] using
    extendedTrace_transported_eq_of_normalizer M τ hτ T hT hker A B hA hB
      hAinj hAadj hBinj hBadj hD hTA p hp hP

end Invariant233.NormalTracialTransport

end

end OAI
