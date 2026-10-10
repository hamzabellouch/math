import OAI.NumberTheory.Ostmann.Supply.FourierIsometry
import OAI.NumberTheory.Ostmann.Supply.SpectralConcentration

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

def coordinateSpace (E : Finset (ZMod p)) : Submodule ℂ H where
  carrier := {f | ∀ v, v ∉ E → f v = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg v hv; simp [hf v hv,hg v hv]
  smul_mem' := by intro c f hf v hv; simp [hf v hv]

def frequencySpace (E : Finset (ZMod p)) : Submodule ℂ H :=
  (coordinateSpace E).comap unitaryDFTLinear

def spectralProjection (E : Finset (ZMod p)) : H →L[ℂ] H :=
  (frequencySpace E).starProjection

def maskedFourier (E : Finset (ZMod p)) (f : H) : H :=
  fourierEquiv.symm (WithLp.toLp 2 (fun v => if v ∈ E then unitaryDFT f v else 0))

theorem fourier_maskedFourier (E : Finset (ZMod p)) (f : H) (v : ZMod p) :
    unitaryDFT (maskedFourier E f) v = if v ∈ E then unitaryDFT f v else 0 := by
  rw [← fourierEquiv_apply]
  simp only [maskedFourier, LinearIsometryEquiv.apply_symm_apply, PiLp.toLp_apply]

theorem maskedFourier_mem (E : Finset (ZMod p)) (f : H) :
    maskedFourier E f ∈ frequencySpace E := by
  intro v hv
  change unitaryDFT (maskedFourier E f) v = 0
  rw [fourier_maskedFourier, ite_eq_right hv]

theorem spectralProjection_eq_maskedFourier (E : Finset (ZMod p)) (f : H) :
    spectralProjection E f = maskedFourier E f := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (maskedFourier_mem E f)
  intro w hw
  rw [← fourierEquiv_inner, PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro v hv
  have he : fourierEquiv (f-maskedFourier E f) v =
      unitaryDFT f v - (if v ∈ E then unitaryDFT f v else 0) := by
    rw [map_sub, PiLp.sub_apply, fourierEquiv_apply, fourierEquiv_apply,
      fourier_maskedFourier]
  rw [he]
  by_cases hvE : v ∈ E
  · simp [hvE]
  · have hwv : fourierEquiv w v = 0 := hw v hvE
    simp [hwv]

theorem spectralProjection_norm_le (E : Finset (ZMod p)) :
    ‖spectralProjection E‖ ≤ 1 := (frequencySpace E).starProjection_norm_le

theorem spectralProjection_fourier (E : Finset (ZMod p)) (f : H) (v : ZMod p) :
    unitaryDFT (spectralProjection E f) v =
      if v ∈ E then unitaryDFT f v else 0 := by
  rw [spectralProjection_eq_maskedFourier, fourier_maskedFourier]

end Ostmann.Supply

end

end OAI
