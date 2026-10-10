import Mathlib
import OAI.Geometry.PrescribedPotential.LocalizedDerivations

namespace OAI

/-! Derivative Localization. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

lemma localize_tsupport_image (q : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart q).source) (f : Smooth A) :
    tsupport (localize A q ρ hρ f : EC d → ℂ) ⊆
      (A.euclideanChart q) '' tsupport (ρ : X → ℂ) := by
  apply closure_minimal (localizeFun_support A q ρ f)
  exact ((isClosed_tsupport _).isCompact.image_of_continuousOn
    ((A.euclideanChart q).continuousOn.mono hρ)).isClosed

lemma schwartz_derivative_zero_of_not_tsupport (f : 𝓢(EC d,ℂ)) (v : EC d) {y : EC d}
    (hy : y ∉ tsupport (f : EC d → ℂ)) : (∂_{v} f : 𝓢(EC d,ℂ)) y = 0 := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    (notMem_tsupport_iff_eventuallyEq.mp hy).fderiv_eq]
  simp

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma localizedDerivative_zero_off_function (p : ι) (v : EC d) (f : Smooth A) {x : X}
    (hx : x ∉ tsupport (f : X → ℂ)) : D.localizedDerivative p v f x = 0 := by
  rw [D.localizedDerivative_apply]
  split_ifs with hs
  · have ht := (A.euclideanChart (D.patch p).index).mapsTo hs
    have hc : Tendsto (A.euclideanChart (D.patch p).index).symm
        (𝓝 (A.euclideanChart (D.patch p).index x)) (𝓝 x) := by
      simpa only [(A.euclideanChart (D.patch p).index).left_inv hs] using
        ((A.euclideanChart (D.patch p).index).symm.continuousAt ht).tendsto
    have hh := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto hc
    rw [hh.fderiv_eq]
    simp
  · rfl

lemma localizedDerivative_function_tsupport (p : ι) (v : EC d) (f : Smooth A) :
    tsupport (D.localizedDerivative p v f : X → ℂ) ⊆ tsupport (f : X → ℂ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hh
  exact hx (D.localizedDerivative_zero_off_function p v f hh)

lemma derivativeWeight_support (p : ι) (v : EC d) :
    tsupport (D.localizedDerivative p v (D.localizers.weight p) : X → ℂ) ⊆
      (A.euclideanChart (D.patch p).index).source := by
  exact (D.localizedDerivative_function_tsupport p v _).trans
    (by rw [← D.index_eq]; exact D.localizers.support_sub p)

lemma forcing_derivative (p : ι) (v : EC d) (f : Smooth A) :
    (∂_{v} (D.forcing p f) : 𝓢(EC d,ℂ)) =
      localize A (D.patch p).index (D.localizedDerivative p v (D.localizers.weight p))
        (D.derivativeWeight_support p v) f + D.forcing p (D.localizedDerivative p v f) := by
  let q := (D.patch p).index
  let e := A.euclideanChart q
  let ρ := D.localizers.weight p
  have hρ : tsupport (ρ : X → ℂ) ⊆ e.source := by
    change tsupport (D.localizers.weight p : X → ℂ) ⊆
      (A.euclideanChart (D.patch p).index).source
    rw [← D.index_eq]
    exact D.localizers.support_sub p
  have heq (h : Smooth A) : D.forcing p h = localize A q ρ hρ h := by
    unfold forcing
    simp only [D.index_eq]
    rfl
  ext y
  by_cases hy : y ∈ e '' tsupport (ρ : X → ℂ)
  · obtain ⟨x,hx,rfl⟩ := hy
    have hs := hρ hx
    have ht := e.mapsTo hs
    have hf : (D.forcing p f : EC d → ℂ) =ᶠ[𝓝 (e x)]
        (fun y => ρ (e.symm y) * f (e.symm y)) := by
      filter_upwards [e.open_target.mem_nhds ht] with z hz
      rw [heq,localize_apply,localizeFun_apply A ρ f hz]
    have hdρ := ((ρ.smooth q).contDiffAt (e.open_target.mem_nhds ht)).differentiableAt (by simp)
    have hdf := ((f.smooth q).contDiffAt (e.open_target.mem_nhds ht)).differentiableAt (by simp)
    change DifferentiableAt ℝ (fun y => ρ (e.symm y)) (e x) at hdρ
    change DifferentiableAt ℝ (fun y => f (e.symm y)) (e x) at hdf
    have hloc (σ : Smooth A)
        (hσ : tsupport (σ : X → ℂ) ⊆ e.source) (fh : Smooth A) :
        localize A q σ hσ fh (e x) = σ x * fh x := by
      rw [localize_apply,localizeFun_apply A σ fh ht,e.left_inv hs]
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,hf.fderiv_eq,
      fderiv_fun_mul hdρ hdf]
    change ρ (e.symm (e x)) * fderiv ℝ (fun y => f (e.symm y)) (e x) v +
      f (e.symm (e x)) * fderiv ℝ (fun y => ρ (e.symm y)) (e x) v =
      localize A q (D.localizedDerivative p v ρ) (D.derivativeWeight_support p v) f (e x) +
      D.forcing p (D.localizedDerivative p v f) (e x)
    rw [hloc,heq,hloc,e.left_inv hs,D.localizedDerivative_apply,
      D.localizedDerivative_apply]
    have hs' : x ∈ (A.euclideanChart (D.patch p).index).source := hs
    simp only [ite_eq_left hs']
    change _ = (D.cutoff p).realPart (e x) *
      fderiv ℝ (fun y => ρ (e.symm y)) (e x) v * f x +
      ρ x * ((D.cutoff p).realPart (e x) * fderiv ℝ (fun y => f (e.symm y)) (e x) v)
    rw [ChartCutoff.realPart_apply,D.cutoff_one p x hx]
    simp only [Complex.one_re,Complex.ofReal_one,one_mul]
    ring
  · have hz : y ∉ tsupport (D.forcing p f : EC d → ℂ) := by
      rw [heq]
      exact fun hh => hy (localize_tsupport_image q ρ hρ f hh)
    rw [schwartz_derivative_zero_of_not_tsupport _ v hz]
    have hz₁ : localize A q (D.localizedDerivative p v ρ) (D.derivativeWeight_support p v) f y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hh
      apply hy
      obtain ⟨x,hx,hxy⟩ := localize_tsupport_image q (D.localizedDerivative p v ρ)
        (D.derivativeWeight_support p v) f hh
      exact ⟨x,D.localizedDerivative_function_tsupport p v ρ hx,hxy⟩
    have hz₂ : D.forcing p (D.localizedDerivative p v f) y = 0 := by
      rw [heq]
      apply image_eq_zero_of_notMem_tsupport
      exact fun hh => hy (localize_tsupport_image q ρ hρ _ hh)
    change 0 = localize A q (D.localizedDerivative p v ρ) (D.derivativeWeight_support p v) f y +
      D.forcing p (D.localizedDerivative p v f) y
    rw [hz₁,hz₂,add_zero]

end GluingData
end GlobalElliptic

end
end

end OAI
