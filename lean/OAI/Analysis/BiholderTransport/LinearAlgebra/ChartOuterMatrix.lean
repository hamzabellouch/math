import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.FrameMetric
import OAI.Analysis.BiholderTransport.LinearAlgebra.OuterActiveMatrix

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ChartOuterMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance chartOuterFinite (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance chartOuterComplete (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _

lemma WeakMTW.exists_uniform_chart_outer_matrix
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → Continuous φ → StrictMono φ →
      ∀ (a:M) (b p:Model n),b∈(extChartAt 𝓘(ℝ,Model n) a).target →
      let z:TangentBundle 𝓘(ℝ,Model n) M:=⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,chartFiberInverse a b p⟩
      ∀ l:ℝ,z.2∈activeLogs (φ ∘ uv.2) z.1 →
      ContDiffAt ℝ 2 φ (uv.2 (riemannianExp z.1 z.2)) →
      HasDerivAt φ l (uv.2 (riemannianExp z.1 z.2)) → 1 < l →
      iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2)) ≤ 0 →
      ∀ B:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,B d e=B e d) → (∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>φ (uv.2 (movingNormal a (b,p+d)))+
        ‖chartFiberInverse a b (p+d)‖^2/2) 0 B →
      ∃V:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
        (∀d,B d d-(iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2))/l^2)*
          (frameMetric a b p d)^2 ≤ inner ℝ (V d) d) ∧
        0 < expJacobian (n:=n) z.1 z.2 ∧
        0 < expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2) ∧
        expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2)*V.det ≤
          (chartFiberInverse a b).toLinearMap.normDet^2*l^n*K*(expJacobian (n:=n) z.1 z.2)^2 := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_active_outer_matrix hlam hcap
  refine ⟨K,hK,?_⟩
  intro x0 uv φ huv hφ hm a b p hb z l ha hφ2 hd hl hconc B hBs hB hjet
  let x:M:=(extChartAt 𝓘(ℝ,Model n) a).symm b
  let T:=trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  have hx:x∈T.baseSet:=by
    simpa only [x,T,TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  let e:=T.continuousLinearEquivAt ℝ x hx
  let A:=chartFiberInverse a b
  have hAe:(A:Model n → TangentSpace 𝓘(ℝ,Model n) x)=e.symm:=
    (T.symm_continuousLinearEquivAt_eq hx).symm
  have hEA (d:Model n):e (A d)=d:=by rw [hAe]; exact e.apply_symm_apply d
  have hAE (d:TangentSpace 𝓘(ℝ,Model n) x):A (e d)=d:=by rw [hAe]; exact e.symm_apply_apply d
  let C:=pullBilinear B e.toContinuousLinearMap
  have hC:HasLowerSecondTaylor (fun d:TangentSpace 𝓘(ℝ,Model n) x=>
      φ (uv.2 (riemannianExp x (A p+d)))+‖A p+d‖^2/2) 0 C:=by
    convert hjet.comp_stationary e.hasFDerivAt e.map_zero using 1
    funext d
    simp only [movingNormal_eq hb,map_add]
    change φ (uv.2 (riemannianExp x (A p+d)))+‖A p+d‖^2/2=
      φ (uv.2 (riemannianExp x (A p+A (e d))))+‖A p+A (e d)‖^2/2
    rw [hAE]
  obtain ⟨V,hVs,hVp,hgain,hσ,hσs,hdet⟩:=HK x0 uv φ huv hφ hm z l ha hφ2 hd hl hconc
    C (fun d f=>hBs _ _) (fun d=>hB _) hC
  let W:=A.adjoint.comp (V.comp A)
  have hdim:Module.finrank ℝ (Model n)=Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x):=by
    rw [tangent_finrank,finrank_euclideanSpace_fin]
  have hP:=det_positive_hessian_pullback (B:=A) (W:=V) hdim
    (chartFiberInverse_injective hb) hVs hVp (show (0:ℝ)<1 by norm_num)
  simp only [one_smul,one_pow,one_mul] at hP
  refine ⟨W,?_,hP.1,?_,hσ,hσs,?_⟩
  · intro d f
    simp only [W,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,hVs]
  · intro d
    have H:=hgain (A d)
    simpa only [C,pullBilinear_apply,ContinuousLinearEquiv.coe_coe,hEA,
      frameMetric_apply hb,W,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left] using H
  · change _*(A.adjoint.comp (V.comp A)).det≤_
    rw [hP.2]
    have H:=mul_le_mul_of_nonneg_left hdet (sq_nonneg A.toLinearMap.normDet)
    nlinarith only [H]
end ChartOuterMatrix
end WeakMTWTransport

end
end

end OAI
