import Mathlib
import OAI.Geometry.PrescribedPotential.NonlinearLocalCoordinates
import OAI.Geometry.PrescribedPotential.NonlinearRemainderStrong
import OAI.Geometry.PrescribedPotential.PotentialDensityDifferential
import OAI.Geometry.PrescribedPotential.RealSobolev

namespace OAI

/-! Nonlinear Core Commutator. -/

section

 

noncomputable section
open Set Filter Topology Matrix LineDeriv
open scoped ContDiff SchwartzMap Classical Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma regularityError_source (p : ι) (v : EC d) (f : Smooth A) (i j : Fin d) {x : X}
    (hx : x ∈ (A.euclideanChart (D.patch p).index).source)
    (hκ : A.euclideanChart (D.patch p).index x ∈ tsupport (D.cutoff p : EC d → ℂ)) :
    D.regularityError p v i j f x = hessianLocalizedError (D.cutoff p).realPart.val v i j
      (localize A (D.patch p).index (cutoffGlobal (D.patch p).index (D.regularityOuter p))
        (cutoffGlobal_support _ _) f) (A.euclideanChart (D.patch p).index x) := by
  change globalize (D.patch p).index (D.regularityCutoff p) _ x = _
  rw [globalize_apply,ite_eq_left hx,(D.regularityCutoff_one p hκ).eq_of_nhds,one_mul]
  rfl

lemma nonlinear_commutator_on_support (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (φ : SmoothRealFunction A) {x : X}
    (hx : x ∈ (A.euclideanChart (D.patch p).index).source)
    (hκ : A.euclideanChart (D.patch p).index x ∈ tsupport (D.cutoff p : EC d → ℂ)) :
    D.localizers.strong (k : ℝ)
      (fderiv ℝ (D.completedVolume k hk) (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ))
        (D.localizers.embed ((k : ℝ)+2) (D.localizedDerivative p v (Smooth.ofReal φ)))) x =
      D.localizedDerivative p v (Smooth.ofReal (g.potentialDensity φ)) x +
      D.localizers.strong (k : ℝ)
        (D.nonlinearRemainder k hk p v (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ))) x := by
  let q := (D.patch p).index
  let e := A.euclideanChart q
  let y := e x
  let f := localize A q (cutoffGlobal q (D.regularityOuter p)) (cutoffGlobal_support _ _) (Smooth.ofReal φ)
  let κ : 𝓢(EC d, ℝ) := SchwartzMap.postcompCLM Complex.reCLM (D.cutoff p).val
  let G : EC d → Matrix (Fin d) (Fin d) ℂ := fun z => g.matrix q (coordinateEquiv d z)
  let B : EC d → ℂ := fun z => (G z).det⁻¹
  let ψ := (D.realLocalizedDerivative p v (RealSmooth.ofReal φ)).source
  have hψ : Smooth.ofReal ψ = D.localizedDerivative p v (Smooth.ofReal φ) :=
    RealSmooth.ofReal_source _
  have ht : y ∈ e.target := e.mapsTo hx
  have hec : coordinateEquiv d y = A.chart q x := by
    simp only [y,e,ComplexAtlas.euclideanChart_apply,ContinuousLinearEquiv.apply_symm_apply]
  have hf : (f : EC d → ℂ) =ᶠ[𝓝 y] Smooth.ofReal φ ∘ e.symm :=
    localize_cutoff_nhds q (D.regularityOuter p) (Smooth.ofReal φ) ht
      (D.regularityOuter_inner p hκ)
  have hH : NonlinearHessian.hessianMatrix f y = φ.hessian q (A.chart q x) := by
    rw [← hec]
    exact (hessianMatrix_source_nhds q φ f ht hf).eq_of_nhds
  have hck : NonlinearHessian.complexCutoff κ = (D.cutoff p).realPart.val := by
    ext z
    rfl
  have hHψ : NonlinearHessian.hessianMatrix
      (SchwartzMap.smulLeftCLM ℂ (NonlinearHessian.complexCutoff κ) (∂_{v} f)) y =
      ψ.hessian q (A.chart q x) := by
    rw [hck,← hec]
    ext i j
    apply hessianEntrySchwartz_source q ψ _ ht
    rw [hψ]
    exact (D.localizedDerivative_local_regularity p v (Smooth.ofReal φ) ht).symm
  have hG : DifferentiableAt ℝ G y :=
    ((metric_euclidean_smooth g q).contDiffAt (e.open_target.mem_nhds ht)).differentiableAt (by simp)
  have hB : DifferentiableAt ℝ B y :=
    ((inverseDet_euclidean_smooth g q).contDiffAt (e.open_target.mem_nhds ht)).differentiableAt (by simp)
  have hden := density_local_schwartz g q φ f ht hf
  have hδden : D.localizedDerivative p v (Smooth.ofReal (g.potentialDensity φ)) x =
      (κ y : ℂ) * fderiv ℝ (fun z => B z * (G z + NonlinearHessian.hessianMatrix f z).det) y v := by
    rw [D.localizedDerivative_apply,ite_eq_left hx,hden.fderiv_eq]
    rfl
  have hM (i j : Fin d) : D.regularityMetric p i j x = G y i j := by
    have hh := (D.regularityMetric_local p i j hκ).eq_of_nhds
    change D.regularityMetric p i j (e.symm (e x)) = G y i j at hh
    rwa [e.left_inv hx] at hh
  have hBv : D.regularityInverseDet p x = B y := by
    have hh := (D.regularityInverseDet_local p hκ).eq_of_nhds
    change D.regularityInverseDet p (e.symm (e x)) = B y at hh
    rwa [e.left_inv hx] at hh
  have hDM (i j : Fin d) : D.localizedDerivative p v (D.regularityMetric p i j) x =
      (κ y : ℂ) * (fderiv ℝ G y v i j) := by
    rw [D.localizedDerivative_apply,ite_eq_left hx,(D.regularityMetric_local p i j hκ).fderiv_eq]
    have hd : fderiv ℝ (fun z => G z i j) y v = fderiv ℝ G y v i j := by
      rw [fderiv_apply (differentiableAt_pi.mp hG i),fderiv_apply hG]
      rfl
    change (κ y : ℂ) * fderiv ℝ (fun z => G z i j) y v = _
    rw [hd]
  have hDB : D.localizedDerivative p v (D.regularityInverseDet p) x =
      (κ y : ℂ) * fderiv ℝ B y v := by
    rw [D.localizedDerivative_apply,ite_eq_left hx,(D.regularityInverseDet_local p hκ).fderiv_eq]
    rfl
  rw [← hψ,D.completedVolumeDerivative_source k hk φ ψ q (by simpa [q] using hx),
    D.nonlinearRemainder_strong_embed,hδden,hBv,hDB]
  have hmat : (fun (i j : Fin d) => D.regularityMetric p i j x +
      D.regularityHessian p i j (Smooth.ofReal φ) x) = G y + NonlinearHessian.hessianMatrix f y := by
    ext i j
    rw [hM,D.regularityHessian_source p φ i j hx hκ,hH]
    rfl
  have herr : (fun (i j : Fin d) => D.regularityError p v i j (Smooth.ofReal φ) x -
      D.localizedDerivative p v (D.regularityMetric p i j) x) =
      NonlinearHessian.cutoffHessianError κ v f y - κ y • fderiv ℝ G y v := by
    ext i j
    rw [D.regularityError_source p v (Smooth.ofReal φ) i j hx hκ,hDM]
    change hessianLocalizedError (D.cutoff p).realPart.val v i j f y -
      (κ y : ℂ) * fderiv ℝ G y v i j =
      hessianLocalizedError (NonlinearHessian.complexCutoff κ) v i j f y -
      κ y • (fderiv ℝ G y v i j)
    rw [hck,Complex.real_smul]
  rw [hmat,herr]
  have hh := NonlinearHessian.determinant_cutoff_commutator κ v f B G y hB hG
  rw [hHψ] at hh
  simpa only [B,G,hec,hH,add_sub_assoc] using hh

end GluingData
end GlobalElliptic

end
end

end OAI
