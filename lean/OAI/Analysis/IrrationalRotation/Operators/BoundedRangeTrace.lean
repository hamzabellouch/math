import OAI.Analysis.IrrationalRotation.Operators.ProjectionMeetTrace

namespace OAI

noncomputable section
namespace Invariant233.BoundedRangeTrace
open ProjectionMeetTrace TracialProjectionTransport
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kernel_projection_mem (M : VonNeumannAlgebra H)
    (A : H →L[ℂ] H) (hA : A ∈ M) : A.ker.starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff isStarProjection_starProjection M).mpr
  intro W hW
  rw [Submodule.range_starProjection]
  intro x hx
  have hcomm := (VonNeumannAlgebra.mem_commutant_iff.mp hW) A hA
  change A (W x) = 0
  change A x = 0 at hx
  have heq := congrArg (fun B : H →L[ℂ] H => B x) hcomm
  change A (W x) = W (A x) at heq
  rw [heq, hx, map_zero]

theorem kernel_trace_eq (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (A : H →L[ℂ] H) (hA : A ∈ M) :
    vectorTrace ξ A.ker.starProjection = vectorTrace ξ A.adjoint.ker.starProjection := by
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
  have heq := vectorTrace_kernel_eq_adjoint_kernel M ξ htrace (c • A)
    (M.toStarSubalgebra.smul_mem hA c) hn
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

theorem range_closure_eq (A : H →L[ℂ] H) :
    A.range.topologicalClosure = A.adjoint.kerᗮ := by
  simpa only [ContinuousLinearMap.adjoint_adjoint] using A.adjoint.orthogonal_ker.symm

theorem range_trace_eq_of_injective
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (A : H →L[ℂ] H) (hA : A ∈ M) (hinj : Function.Injective A)
    (p : Submodule ℂ H) [CompleteSpace p] (hp : p.starProjection ∈ M) :
    vectorTrace ξ (A * p.starProjection).range.topologicalClosure.starProjection =
      vectorTrace ξ p.starProjection := by
  have hk : (A * p.starProjection).ker = pᗮ := by
    rw [← p.ker_starProjection]
    ext x
    change A (p.starProjection x) = 0 ↔ p.starProjection x = 0
    exact map_eq_zero_iff A hinj
  have ht := kernel_trace_eq M ξ htrace (A * p.starProjection) (mul_mem hA hp)
  simp only [hk] at ht
  simp only [range_closure_eq, vectorTrace_projection_orthogonal, ← ht]
  ring

theorem preimage_trace_eq
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (A : H →L[ℂ] H) (hA : A ∈ M) (hinj : Function.Injective A.adjoint)
    (p : Submodule ℂ H) [CompleteSpace p] (hp : p.starProjection ∈ M) :
    vectorTrace ξ ((1 - p.starProjection) * A).ker.starProjection =
      vectorTrace ξ p.starProjection := by
  have hstar : ((1 - p.starProjection) * A).adjoint =
      A.adjoint * (1 - p.starProjection) := by
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_sub, star_one,
      isStarProjection_starProjection.isSelfAdjoint.star_eq]
  have hk : ((1 - p.starProjection) * A).adjoint.ker = p := by
    rw [hstar]
    ext x
    change A.adjoint (x - p.starProjection x) = 0 ↔ x ∈ p
    rw [map_eq_zero_iff A.adjoint hinj, sub_eq_zero]
    rw [eq_comm]
    exact p.starProjection_eq_self_iff
  have ht := kernel_trace_eq M ξ htrace ((1 - p.starProjection) * A)
    (mul_mem (sub_mem (one_mem M) hp) hA)
  simpa only [hk] using ht

theorem trace_le_transported_of_normalizer
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (T : H →ₗ.[ℂ] H) (A B : H →L[ℂ] H)
    (hA : A ∈ M) (hB : B ∈ M)
    (hAinj : Function.Injective A.adjoint) (hBinj : Function.Injective B)
    (hD : ∀ x, A x ∈ T.domain) (hTA : ∀ x, T ⟨A x, hD x⟩ = B x)
    (p : Submodule ℂ H) [CompleteSpace p] (hp : p.starProjection ∈ M) :
    (vectorTrace ξ p.starProjection).re ≤
      (vectorTrace ξ (InvariantRotation.AffiliatedTransport.transported T p).starProjection).re := by
  let r := ((1 - p.starProjection) * A).ker
  have hr : r.starProjection ∈ M := kernel_projection_mem M _
    (mul_mem (sub_mem (one_mem M) hp) hA)
  have hrt : vectorTrace ξ r.starProjection = vectorTrace ξ p.starProjection :=
    preimage_trace_eq M ξ htrace A hA hAinj p hp
  have hBt := range_trace_eq_of_injective M ξ htrace B hB hBinj r hr
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
  have ht := vectorTrace_projection_mono ξ hle
  simpa only [hBt, hrt] using ht

theorem transported_trace_eq_of_normalizer
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (T : H →ₗ.[ℂ] H) (hT : T.IsFormalAdjoint T) (hker : T.toFun.ker = ⊥)
    (A B : H →L[ℂ] H) (hA : A ∈ M) (hB : B ∈ M)
    (hAinj : Function.Injective A) (hAadj : Function.Injective A.adjoint)
    (hBinj : Function.Injective B) (hBadj : Function.Injective B.adjoint)
    (hD : ∀ x, A x ∈ T.domain) (hTA : ∀ x, T ⟨A x, hD x⟩ = B x)
    (p : Submodule ℂ H) [CompleteSpace p] (hp : p.starProjection ∈ M) :
    vectorTrace ξ (InvariantRotation.AffiliatedTransport.transported T p).starProjection =
      vectorTrace ξ p.starProjection := by
  have hforward := trace_le_transported_of_normalizer M ξ htrace T A B hA hB
    hAadj hBinj hD hTA p hp
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
  have hback := trace_le_transported_of_normalizer M ξ htrace T.inverse B A hB hA
    hBadj hAinj hDinv hTinv pᗮ hpperp
  have horth := InvariantRotation.AffiliatedTransport.inverse_transported_le_orthogonal
    T p hT hker
  have hback' := hback.trans (vectorTrace_projection_mono ξ horth)
  rw [vectorTrace_projection_orthogonal, vectorTrace_projection_orthogonal] at hback'
  have hre : (vectorTrace ξ (InvariantRotation.AffiliatedTransport.transported T p).starProjection).re =
      (vectorTrace ξ p.starProjection).re := by
    simp only [Complex.sub_re] at hback'
    linarith
  rw [vectorTrace_projection_re, vectorTrace_projection_re] at hre
  rw [vectorTrace_projection, vectorTrace_projection]
  exact_mod_cast hre

end Invariant233.BoundedRangeTrace

end

end OAI
