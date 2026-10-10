import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.OuterTrueMatrix
import OAI.Analysis.BiholderTransport.Regularity.ActiveOuter

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterActiveMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance oamFinite (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance oamComplete (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _

lemma WeakMTW.exists_uniform_active_outer_matrix
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → Continuous φ → StrictMono φ →
      ∀ (z:TangentBundle 𝓘(ℝ,Model n) M) (l:ℝ),z.2∈activeLogs (φ ∘ uv.2) z.1 →
      ContDiffAt ℝ 2 φ (uv.2 (riemannianExp z.1 z.2)) →
      HasDerivAt φ l (uv.2 (riemannianExp z.1 z.2)) → 1 < l →
      iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2)) ≤ 0 →
      ∀ B:TangentSpace 𝓘(ℝ,Model n) z.1 →L[ℝ] TangentSpace 𝓘(ℝ,Model n) z.1 →L[ℝ] ℝ,
      (∀d e,B d e=B e d) → (∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>φ (uv.2 (riemannianExp z.1 (z.2+d)))+‖z.2+d‖^2/2) 0 B →
      ∃V:TangentSpace 𝓘(ℝ,Model n) z.1 →L[ℝ] TangentSpace 𝓘(ℝ,Model n) z.1,
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0  <  inner ℝ (V d) d) ∧
        (∀d,B d d-(iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2))/l^2)*
          (inner ℝ z.2 d)^2  ≤  inner ℝ (V d) d) ∧
        0 < expJacobian (n:=n) z.1 z.2 ∧
        0 < expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2) ∧
        expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2)*V.det  ≤
          l^n*K*(expJacobian (n:=n) z.1 z.2)^2 := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_outer_true_matrix hlam hcap
  refine ⟨K,hK,?_⟩
  intro x0 uv φ huv hφc hm z l ha hφ hd hl hconc B hBs hB hjet
  have hnc:=hmtw.active_outer_nonconjugate hlam hcap huv hφc hm ha hφ hd hl hconc
  obtain ⟨G,hG,hact,hagree⟩:=exists_reverse_branch_with_forward_action z hnc
  have hy:riemannianExp z.1 z.2=(reverseRay z).1:=(reverseRay_base z).symm
  have hx:riemannianExp (reverseRay z).1 (reverseRay z).2=z.1:=reverseRay_endpoint z
  have hr:=(reverseRay_minimizing ha.1)
  have hact':∀ᶠ q in 𝓝 z.2,G (riemannianExp z.1 q,z.1)=‖q‖^2/2:=
    (FiberBundle.continuous_totalSpaceMk (Model n)
      (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x) z.1).continuousAt.eventually hact
  obtain ⟨C,V,hCI,hCd,hpair,hVs,hVp,hVeq,hVdet⟩:=HK z.1 (reverseRay z).1 z.2
    (reverseRay z).2 G l hy hx hr hnc (by simpa only [hx] using hG) hact' hagree hl
    x0 uv φ huv hm (by simpa only [reverseRay_base] using hφ)
    (by simpa only [reverseRay_base] using hd) (by simpa only [reverseRay_base] using hconc)
    B hBs hB hjet
  have hl0:0 < l:=zero_lt_one.trans hl
  obtain ⟨m,hm',HM⟩:=exists_branch_divided_baseline hr (inv_pos.mpr hl0)
    (inv_lt_one_of_one_lt₀ hl) hG hagree
  have hJac:0 < expJacobian (n:=n) z.1 z.2:=by
    rw [←hCd]
    apply lt_of_le_of_ne (LinearMap.normDet_nonneg _)
    apply Ne.symm
    rw [ne_eq,LinearMap.normDet_eq_zero_iff_ker_ne_bot,not_not,LinearMap.ker_eq_bot]
    exact hCI
  refine ⟨V,hVs,hVp,?_,hJac,?_,hVdet⟩
  · intro d
    have HH:=HM (C d)
    rw [div_inv_eq_mul,mul_comm (hessianValue _ _ _) l,hx] at HH
    have H0:0 ≤ l*hessianValue (reverseRay z).1 (l⁻¹ • (reverseRay z).2) (C d)-
        fderiv ℝ (fderiv ℝ (fun w=>G (riemannianExp (reverseRay z).1 w,z.1))) 0 (C d) (C d):=
      (mul_nonneg hm'.le (sq_nonneg _)).trans HH
    rw [hVeq,hy]
    linarith only [H0]
  · exact expJacobian_pos_of_injectivityDomain
      (contracted_minimizer_mem_injectivityDomain hr (inv_pos.mpr hl0) (inv_lt_one_of_one_lt₀ hl))
end OuterActiveMatrix
end WeakMTWTransport

end
end

end OAI
