import OAI.Analysis.LipschitzHilbert.Trees.SourceVectorSchwartz
import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketSpectrum

namespace OAI

/-! Coordinate Fourier support of actual planar packets. These lemmas
project the original two-dimensional spectrum without a tensor assumption. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert

def planarSwap (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) f

@[simp] theorem planarSwap_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    planarSwap f z=f z.swap := rfl

def planarVerticalSlice (f : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ) : SchwartzMap ℝ ℂ :=
  planarSchwartzSlice (planarSwap f) x 0

@[simp] theorem planarVerticalSlice_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (x y : ℝ) :
    planarVerticalSlice f x y=f (x,y) := by
  simp only [planarVerticalSlice,planarSchwartzSlice_apply,planarSwap_apply,zero_mul,add_zero,
    Prod.swap_prod_mk]

theorem planarFourier_swap (f : SchwartzMap (ℝ×ℝ) ℂ) (ξ η : ℝ) :
    planarFourier (planarSwap f) (ξ,η)=planarFourier f (η,ξ) := by
  unfold planarFourier
  simp only [planarSwap_apply]
  have h := integral_prod_swap (μ:=volume) (ν:=volume)
    (fun z : ℝ×ℝ => Real.fourierChar (-(z.1*η+z.2*ξ)) • f z)
  simpa only [Prod.fst_swap,Prod.snd_swap,add_comm] using h

theorem planarVerticalSlice_fourier_eq_zero (f : SchwartzMap (ℝ×ℝ) ℂ)
    (x η : ℝ) (hfiber : ∀ ξ, planarFourier f (ξ,η)=0) :
    𝓕 (planarVerticalSlice f x) η=0 := by
  apply planarSchwartzSlice_fourier_eq_zero
  intro ξ
  simpa only [zero_mul,sub_zero,planarFourier_swap] using hfiber ξ

theorem planarHorizontalSlice_fourier_band (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ)
    (hf : ∀ ξ η, planarFourier f (ξ,η)≠0 → |ξ|≤R) (y ξ : ℝ)
    (hne : 𝓕 (planarSchwartzSlice f y 0) ξ≠0) : |ξ|≤R := by
  by_contra hn
  apply hne
  apply planarSchwartzSlice_fourier_eq_zero
  intro η
  simp only [zero_mul,sub_zero]
  by_contra h
  exact hn (hf ξ η h)

theorem planarVerticalSlice_fourier_band (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ)
    (hf : ∀ ξ η, planarFourier f (ξ,η)≠0 → |η|≤R) (x η : ℝ)
    (hne : 𝓕 (planarVerticalSlice f x) η≠0) : |η|≤R := by
  by_contra hn
  apply hne
  apply planarVerticalSlice_fourier_eq_zero
  intro ξ
  by_contra h
  exact hn (hf ξ η h)

/-- Angular and cycles-per-unit cutoffs differ by exactly `2π`. -/
theorem planarAngularFourier_coordinate_bands (f : SchwartzMap (ℝ×ℝ) ℂ) (Rx Ry : ℝ)
    (hf : ∀ ξ η, planarAngularFourier f (ξ,η)≠0 → |ξ|≤Rx ∧ |η|≤Ry) :
    ∀ ξ η, planarFourier f (ξ,η)≠0 →
      |ξ|≤Rx/(2*Real.pi) ∧ |η|≤Ry/(2*Real.pi) := by
  intro ξ η hne
  have hπ : 0<2*Real.pi := by positivity
  have he (t : ℝ) : (2*Real.pi*t)/(2*Real.pi)=t := by field_simp
  have hs := hf (2*Real.pi*ξ) (2*Real.pi*η) (by
    simpa only [planarAngularFourier,he] using hne)
  simp only [abs_mul,abs_of_pos hπ] at hs
  constructor
  · exact (le_div_iff₀ hπ).mpr (by simpa only [mul_comm] using hs.1)
  · exact (le_div_iff₀ hπ).mpr (by simpa only [mul_comm] using hs.2)

theorem planarVerticalSlice_angular_band (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ)
    (hf : ∀ ξ η, planarAngularFourier f (ξ,η)≠0 → |η|≤R) (x η : ℝ)
    (hne : 𝓕 (planarVerticalSlice f x) η≠0) : |η|≤R/(2*Real.pi) := by
  apply planarVerticalSlice_fourier_band f (R/(2*Real.pi)) _ x η hne
  intro ξ η h
  have hπ : 0<2*Real.pi := by positivity
  have he (t : ℝ) : (2*Real.pi*t)/(2*Real.pi)=t := by field_simp
  have hs := hf (2*Real.pi*ξ) (2*Real.pi*η) (by
    simpa only [planarAngularFourier,he] using h)
  rw [abs_mul,abs_of_pos hπ] at hs
  exact (le_div_iff₀ hπ).mpr (by simpa only [mul_comm] using hs)

/-- The manuscript's wedge and positive transverse band give both
coordinate cutoffs on the reference plane. Only the upper selector
separation is needed here. -/
theorem sourcePacket_coordinate_bands (f : SchwartzMap (ℝ×ℝ) ℂ)
    (θ ell w cStar cEta CEta Cb : ℝ)
    (hell : 0<ell) (hw : 0<w) (hcEta : 0<cEta) (hCb : 0≤Cb)
    (hspectrum : ∀ ξ η, planarAngularFourier f (ξ,η)≠0 →
      |ξ+θ*η|≤cStar/ell ∧ cEta≤w*η ∧ w*η≤CEta)
    (hselector : |θ|≤Cb*w/ell) :
    (∀ y ξ, 𝓕 (planarSchwartzSlice f y 0) ξ≠0 →
      |ξ|≤(CEta*Cb+cStar)/(2*Real.pi*ell)) ∧
    (∀ x η, 𝓕 (planarVerticalSlice f x) η≠0 →
      |η|≤CEta/(2*Real.pi*w)) := by
  constructor
  · intro y ξ h
    apply (sourcePacket_fourier_annulus f y 0 θ ell w cStar cEta CEta 0 Cb
      hell hw hcEta le_rfl hCb hspectrum _ h).2
    simpa only [zero_sub,abs_neg,zero_mul,zero_div] using
      And.intro (abs_nonneg θ) hselector
  · intro x η h
    have h' := planarVerticalSlice_angular_band f (CEta/w) (by
      intro ξ η hξη
      have hs := hspectrum ξ η hξη
      have hη : 0≤η := ((mul_pos_iff_of_pos_left hw).mp (hcEta.trans_le hs.2.1)).le
      rw [abs_of_nonneg hη]
      exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hs.2.2)) x η h
    simpa only [div_div,mul_comm w (2*Real.pi)] using h'

variable {κ : Type*} [Fintype κ]

theorem vectorHorizontalSlice_coordinate (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (y : ℝ) (k : κ) :
    (vectorHorizontalSlice f y).postcompCLM (vectorCoordinate k)=
      planarSchwartzSlice (f.postcompCLM (vectorCoordinate k)) y 0 := by
  ext x
  simp only [SchwartzMap.postcompCLM_apply,vectorHorizontalSlice_apply,
    planarSchwartzSlice_apply,zero_mul,add_zero]

theorem vectorVerticalSlice_coordinate (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (x : ℝ) (k : κ) :
    (vectorVerticalSlice f x).postcompCLM (vectorCoordinate k)=
      planarVerticalSlice (f.postcompCLM (vectorCoordinate k)) x := by
  ext y
  simp only [SchwartzMap.postcompCLM_apply,vectorVerticalSlice_apply,planarVerticalSlice_apply]

/-- The same planar scalar-coordinate spectral rectangle controls the
actual vector slices, with no loss depending on their dimension. -/
theorem vector_coordinate_fourier_bands (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (Rx Ry : ℝ)
    (hf : ∀ k ξ η, planarFourier (f.postcompCLM (vectorCoordinate k)) (ξ,η)≠0 →
      |ξ|≤Rx ∧ |η|≤Ry) :
    (∀ y ξ, 𝓕 (vectorHorizontalSlice f y) ξ≠0 → |ξ|≤Rx) ∧
    (∀ x η, 𝓕 (vectorVerticalSlice f x) η≠0 → |η|≤Ry) := by
  constructor
  · intro y ξ hne
    by_contra hn
    apply hne
    ext k
    rw [vector_fourier_coordinate,vectorHorizontalSlice_coordinate]
    have hz : 𝓕 (planarSchwartzSlice (f.postcompCLM (vectorCoordinate k)) y 0) ξ=0 := by
      by_contra h
      exact hn (planarHorizontalSlice_fourier_band _ Rx (fun a b h => (hf k a b h).1) y ξ h)
    exact hz
  · intro x η hne
    by_contra hn
    apply hne
    ext k
    rw [vector_fourier_coordinate,vectorVerticalSlice_coordinate]
    have hz : 𝓕 (planarVerticalSlice (f.postcompCLM (vectorCoordinate k)) x) η=0 := by
      by_contra h
      exact hn (planarVerticalSlice_fourier_band _ Ry (fun a b h => (hf k a b h).2) x η h)
    exact hz

end LipschitzHilbert

end

end OAI
