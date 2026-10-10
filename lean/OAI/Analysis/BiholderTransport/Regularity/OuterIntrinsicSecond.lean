import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.OuterIntrinsicDet

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterIntrinsicSecond
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance oisFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma WeakMTW.exists_uniform_outer_normal_det_bound_second
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0<lam) (hcap:0≤cap) :
    ∃K:ℝ,0<K ∧ ∀ (a:M) (r:TangentSpace 𝓘(ℝ,Model n) a) (G:M×M → ℝ) (l:ℝ),
      r∈minimizingVectors a →
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        (a,riemannianExp a r) →
      (∀ᶠ z in 𝓝 (⟨a,r⟩:TangentBundle 𝓘(ℝ,Model n) M),z.2∈injectivityDomain z.1 →
        (fun q:M×M=>cost q.1 q.2)=ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) → 1<l →
      ∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.2 a) → HasDerivAt φ l (uv.2 a) → iteratedDeriv 2 φ (uv.2 a)≤0 →
      ∀H:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] ℝ,
      (∀d e,H d e=H e d) → (∀d,0≤H d d) →
      HasLowerSecondTaylor (fun w=>φ (uv.2 (riemannianExp a w))+
        G (riemannianExp a w,riemannianExp a r)) 0 H →
      ∃V:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a,
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
        (∀d,inner ℝ (V d) d=H d d+
          (l*hessianValue a (l⁻¹ • r) d-
            fderiv ℝ (fderiv ℝ (fun w=>G (riemannianExp a w,riemannianExp a r))) 0 d d)-
          (iteratedDeriv 2 φ (uv.2 a)/l^2)*(inner ℝ r d)^2) ∧
        expJacobian (n:=n) a (l⁻¹ • r)*V.det≤l^n*K := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_outer_normal_det_bound hlam hcap
  refine ⟨K,hK,?_⟩
  intro a r G l hr hG hagree hl x0 uv φ huv hmono hφ hd hconc H hHs hH hjet
  let vu:=reverseNormalizedPair x0 uv
  let ψ:=fun s:ℝ=>φ (uv.2 x0+s)
  have heq (y:M):uv.2 x0+vu.1 y=uv.2 y:=by
    change uv.2 x0+(uv.2 y+-uv.2 x0)=uv.2 y
    ring
  have hψ:ContDiffAt ℝ 2 ψ (vu.1 a):=
    ((heq a).symm ▸ hφ).comp _ (contDiffAt_const.add contDiffAt_id)
  have hdψ:HasDerivAt ψ l (vu.1 a):=by
    have hd':HasDerivAt φ l (uv.2 x0+vu.1 a):=(heq a).symm ▸ hd
    simpa only [mul_one,Function.comp_def,ψ] using
      hd'.comp _ ((hasDerivAt_id _).const_add (uv.2 x0))
  have hec:iteratedDeriv 2 ψ (vu.1 a)=iteratedDeriv 2 φ (uv.2 a):=by
    dsimp only [ψ]
    rw [iteratedDeriv_comp_const_add]
    dsimp only
    rw [heq]
  have HM:=HK a r G l hr hG hagree hl x0 vu ψ (densityDualClass_reverse hlam huv)
    (fun _ _ h=>hmono (by linarith)) hψ hdψ (by rw [hec]; exact hconc) H hHs hH
    (by simpa only [ψ,heq] using hjet)
  simpa only [hec] using HM
end OuterIntrinsicSecond
end WeakMTWTransport

end
end

end OAI
