import Mathlib
import OAI.Analysis.Conductivity.Flux.LinearTensorEllipticity
import OAI.Analysis.Conductivity.Fourier.AngularInverseTensor

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

def undoAngularOutput (A : Matrix (Fin 2) (Fin 2) ℤ) (d lam : ℝ) :
    (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight (fun i : Fin 2 =>
    (LinearEquiv.smulOfNeZero ℝ ℝ
      (if i=0 then sqrt (angularNormalization A) else exp (-lam*d))
      (by split_ifs; exact (sqrt_pos.mpr (angularNormalization_pos A)).ne'; exact exp_ne_zero _)).toContinuousLinearEquiv)

@[simp] lemma undoAngularOutput_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (d lam : ℝ)
    (v : Fin 2 → ℝ) (i : Fin 2) :
    undoAngularOutput A d lam v i=
      (if i=0 then sqrt (angularNormalization A) else exp (-lam*d))*v i := rfl

def undoAngularTranslation (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ) (d : ℝ) : Coord3 :=
  ![d,0,0]+angularNormalizedLift A ![0,θ 0,θ 1]

lemma undoAngularPoint_eq_affine {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d : ℝ) (x : Coord3) :
    (angularNormalizedEquiv A hA).symm (x-undoAngularTranslation A θ d)=
      undoAngularPoint A θ d x := by
  unfold undoAngularTranslation
  rw [←sub_sub,map_sub,angularNormalizedEquiv_symm_apply,
    angularNormalizedEquiv_symm_apply,angularInverseLift_normalized hA]
  rfl

lemma undoAngular_domain {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d : ℝ) :
    ((fun x => x-undoAngularTranslation A θ d) ⁻¹'
      ((angularNormalizedEquiv A hA).symm ⁻¹' {y : Coord3 | 0<y 0}))=
      {x : Coord3 | d<x 0} := by
  ext x
  change (0<(angularNormalizedEquiv A hA).symm (x-undoAngularTranslation A θ d) 0) ↔ _
  rw [undoAngularPoint_eq_affine hA,undoAngularPoint_zero]
  exact (div_pos_iff_of_pos_right (sqrt_pos.mpr (angularNormalization_pos A))).trans sub_pos

namespace WeakFiniteTensorPair

def onEq {U V : Set Coord3} (w : WeakFiniteTensorPair U) (h : U=V) :
    WeakFiniteTensorPair V where
  v := w.v
  E := w.E
  symm := w.symm
  smooth := w.smooth
  measurable := w.measurable
  elliptic := w.elliptic
  regular := by simpa only [←h] using w.regular
  G := w.G
  flux_C1 := w.flux_C1
  constitution := w.constitution
  weak j ψ hc hs := w.weak j ψ hc (by simpa only [h] using hs)

def undoAngular {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d lam : ℝ) (w : WeakFiniteTensorPair {y : Coord3 | 0<y 0}) :
    WeakFiniteTensorPair {x : Coord3 | d<x 0} := by
  let z := ((w.linear (angularNormalizedEquiv A hA).symm
    (undoAngularOutput A d lam)).translate (undoAngularTranslation A θ d) ![d,0]).scaleTensor
      (angularNormalization A)⁻¹ (inv_pos.mpr (angularNormalization_pos A))
  exact z.onEq (undoAngular_domain hA θ d)

lemma undoAngular_v {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d lam : ℝ) (w : WeakFiniteTensorPair {y : Coord3 | 0<y 0}) :
    (w.undoAngular hA θ d lam).v=undoAngularValue A θ d lam w.v := by
  funext x
  change undoAngularOutput A d lam (w.v ((angularNormalizedEquiv A hA).symm
    (x-undoAngularTranslation A θ d)))+![d,0]=_
  rw [undoAngularPoint_eq_affine hA]
  ext i
  fin_cases i <;> simp [undoAngularValue]

lemma undoAngular_E {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d lam : ℝ) (w : WeakFiniteTensorPair {y : Coord3 | 0<y 0}) :
    (w.undoAngular hA θ d lam).E=undoAngularTensor A θ d w.E := by
  funext x
  change (angularNormalization A)⁻¹ •
    linearTensorPullback (angularNormalizedEquiv A hA).symm w.E (x-undoAngularTranslation A θ d)=_
  rw [linearTensorPullback,ContinuousLinearEquiv.symm_symm,
    operatorMatrix_angularNormalizedEquiv,undoAngularPoint_eq_affine hA]
  rfl

end WeakFiniteTensorPair
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

theorem general_mode_weak_finite_ending {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h₀ : Fin 2 → ℤ} (hh₀ : h₀≠0)
    {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s h₀+gb≤torusRate s h)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ),Q.det=1 ∧
      ∃ p T : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧ 7<T ∧
      ∃ w : WeakFiniteTensorPair {y : Coord3 | 0<y 0},
        AngularPeriodic (2*Real.pi) w.v ∧ AngularPeriodic (2*Real.pi) w.E ∧
        (∀ x,x 0∈Icc 0 (1/2) → w.v x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0
              (sqrt (angularNormalization Q)*(10+1/p)) a) pa
              (angularNormalizedLift Q (angularRealTranslation θ x))/sqrt (angularNormalization Q),
            flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift Q (angularRealTranslation θ x))+
              flatFourier s (normalizedFourierCoefficients s (torusRate s h₀)
                (sqrt (angularNormalization Q)*(10+1/p)) b) pb
                (angularNormalizedLift Q (angularRealTranslation θ x))]) ∧
        (∀ x,x 0∈Icc 0 (1/2) → w.E x=flatBackgroundTensor (normalizedAngularTensor s Q)) ∧
        (∀ x,T≤x 0 → w.v x=![x 0,0]) ∧
        (∀ x,7≤x 0 → w.E x*ᵥPi.single 0 1=Pi.single 0 1) := by
  obtain ⟨Q,θ,k,hQ,_hk,_he,p,T,c,C,hp,hpδ,hT,hc,hcC,
    v,E,hsym,hv,hEm,hvp,hEp,hbound,hvin,hEin,hterm,hnormal,hreg,⟨G,hGc,hG⟩,hpde⟩ :=
    general_mode_finite_ending_raw_normal hs hh₀ hA hB ha hb hga hgb hra hrb hδ
  let w : WeakFiniteTensorPair {y : Coord3 | 0<y 0} := {
    v := v, E := E, symm := hsym, smooth := hv, measurable := hEm,
    elliptic := ⟨c,C,hc,hcC,hbound⟩, regular := hreg,
    G := G, flux_C1 := hGc, constitution := hG,
    weak := by
      intro j ψ hψ hψs
      calc
        (∫ x,fderiv ℝ ψ.val x ((G x).col j))=
            ∫ x,∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
              (smoothDirection (Pi.single i 1) ψ).val x := by
          apply integral_congr_ae
          filter_upwards [hG] with x hx
          rw [coordinate_flux_pairing (fun y => (G y).col j) ψ x,hx]
        _ = 0 := (hpde j ψ hψ hψs).2 }
  exact ⟨Q,θ,hQ,p,T,hp,hpδ,hT,w,hvp,hEp,hvin,hEin,hterm,hnormal⟩

end ScalarConductivity

end
end

end OAI
