import OAI.Analysis.PlanarPacking.FourierPairSupport
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def qComplexSchwartz (p : CardinalData) : SchwartzMap Plane ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (qSchwartz p)
lemma qComplexSchwartz_apply (p : CardinalData) (x : Plane) :
    qComplexSchwartz p x=(qSchwartz p x:ℂ) := rfl
noncomputable def kSchwartz (p : CardinalData) : SchwartzMap Plane ℝ :=
  SchwartzMap.postcompCLM Complex.reCLM (𝓕 (qComplexSchwartz p))
lemma kSchwartz_apply (p : CardinalData) (x : Plane) :
    kSchwartz p x=Real.exp (-Real.pi*h*(b*‖x‖^2))*K p 0 (b*‖x‖^2) := by
  change (𝓕 (qComplexSchwartz p) x).re=_
  rw [SchwartzMap.fourier_coe]
  change (𝓕 (fun x : Plane => (qSchwartz p x:ℂ)) x).re=_
  rw [qSchwartz_fourier]
  rfl
lemma qComplexSchwartz_even (p : CardinalData) (x : Plane) :
    qComplexSchwartz p (-x)=qComplexSchwartz p x := by
  simp only [qComplexSchwartz_apply,qSchwartz_apply,norm_neg]
lemma qComplexSchwartz_fourier_even (p : CardinalData) (x : Plane) :
    𝓕 (qComplexSchwartz p) (-x)=𝓕 (qComplexSchwartz p) x := by
  simp only [SchwartzMap.fourier_coe]
  change 𝓕 (fun x : Plane => (qSchwartz p x:ℂ)) (-x)=_
  rw [qSchwartz_fourier]
  change _=𝓕 (fun x : Plane => (qSchwartz p x:ℂ)) x
  rw [qSchwartz_fourier,norm_neg]
lemma fourier_twice_q (p : CardinalData) (x : Plane) :
    𝓕 (𝓕 (qComplexSchwartz p)) x=qComplexSchwartz p x := by
  have he := congrArg (fun f : SchwartzMap Plane ℂ => f (-x))
    (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap Plane ℂ) (qComplexSchwartz p))
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq_fourier_neg,neg_neg] at he
  rw [SchwartzMap.fourier_coe]
  exact he.trans (qComplexSchwartz_even p x)
lemma kSchwartz_fourier (p : CardinalData) (x : Plane) :
    𝓕 (fun x : Plane => (kSchwartz p x:ℂ)) x=(qSchwartz p x:ℂ) := by
  change 𝓕 (fun x => ((𝓕 (qComplexSchwartz p) x).re:ℂ)) x=_
  rw [fourier_re_even (𝓕 (qComplexSchwartz p)).integrable
    (qComplexSchwartz_fourier_even p)]
  rw [← SchwartzMap.fourier_coe,fourier_twice_q,qComplexSchwartz_apply]
  rfl
noncomputable def pairLeft (p q : CardinalData) : SchwartzMap Plane ℝ := qSchwartz p+kSchwartz q
noncomputable def pairRight (p q : CardinalData) : SchwartzMap Plane ℝ := qSchwartz q+kSchwartz p
lemma pairLeft_apply (p q : CardinalData) (x : Plane) :
    pairLeft p q x=Real.exp (-Real.pi*h*(b*‖x‖^2))*(cardinal p (b*‖x‖^2)+K q 0 (b*‖x‖^2)) := by
  change qSchwartz p x+kSchwartz q x=_
  rw [qSchwartz_apply,kSchwartz_apply,mul_add]
lemma pairRight_apply (p q : CardinalData) (x : Plane) :
    pairRight p q x=Real.exp (-Real.pi*h*(b*‖x‖^2))*(cardinal q (b*‖x‖^2)+K p 0 (b*‖x‖^2)) :=
  pairLeft_apply q p x
lemma pair_fourier (p q : CardinalData) (x : Plane) :
    𝓕 (fun x : Plane => (pairLeft p q x:ℂ)) x=(pairRight p q x:ℂ) := by
  have hi1 : Integrable (fun x : Plane => (qSchwartz p x:ℂ)) :=  Complex.ofRealCLM.integrable_comp ((qSchwartz p).integrable (μ := volume))
  have hi2 : Integrable (fun x : Plane => (kSchwartz q x:ℂ)) :=  Complex.ofRealCLM.integrable_comp ((kSchwartz q).integrable (μ := volume))
  change 𝓕 (fun x : Plane => ((qSchwartz p x+kSchwartz q x:ℝ):ℂ)) x=_
  simp only [Complex.ofReal_add]
  rw [fourier_add_integrable hi1 hi2,qSchwartz_fourier,kSchwartz_fourier]
  change _=((qSchwartz q x+kSchwartz p x:ℝ):ℂ)
  rw [kSchwartz_apply,Complex.ofReal_add,add_comm]
lemma pairLeft_radial (p q : CardinalData) {x y : Plane} (hxy : ‖x‖=‖y‖) :
    pairLeft p q x=pairLeft p q y := by rw [pairLeft_apply,pairLeft_apply,hxy]
lemma pairRight_radial (p q : CardinalData) {x y : Plane} (hxy : ‖x‖=‖y‖) :
    pairRight p q x=pairRight p q y := pairLeft_radial q p hxy
end SharpPlanar

end OAI
