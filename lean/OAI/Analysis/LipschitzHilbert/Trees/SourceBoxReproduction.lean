import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarVectorReproduction

namespace OAI

/-! Uniform reproduction on a physical rectangle. The two spectra are
properties of the actual coordinate restrictions, and all vector
members are controlled by one scalar maximal function. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert
open DyadicLineGrid
variable {κ : Type*} [Fintype κ]

def coordinateBox (cx cy rx ry : ℝ) : Set (ℝ×ℝ) :=
  {z | |z.1-cx|≤rx ∧ |z.2-cy|≤ry}

theorem coordinateBox_measurable (cx cy rx ry : ℝ) :
    MeasurableSet (coordinateBox cx cy rx ry) := by
  exact (measurableSet_le (show Measurable (fun z : ℝ×ℝ => |z.1-cx|) by fun_prop) measurable_const).inter
    (measurableSet_le (show Measurable (fun z : ℝ×ℝ => |z.2-cy|) by fun_prop) measurable_const)

theorem planar_reproduction_kernel_bound
    (Kx Ky : SchwartzMap ℝ ℂ) (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (Rx Ry cx cy rx ry : ℝ) (hrx : 0<rx) (hry : 0<ry)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ y ξ, 𝓕 (vectorHorizontalSlice f y) ξ≠0 → |ξ|≤Rx/rx)
    (hFy : ∀ x η, 𝓕 (vectorVerticalSlice f x) η≠0 → |η|≤Ry/ry)
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (B : ℝ) (hUb : ∀ p, ‖U p‖≤B)
    (hFU : ∀ p, ‖f p‖≤U p) (w : ℝ×ℝ) (hw : w∈coordinateBox cx cy rx ry) :
    ‖f w‖≤(16*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)*
      ∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
        ∂volume.prod volume := by
  let Cx := schwartzEnvelopeConstant Kx 1
  let Cy := schwartzEnvelopeConstant Ky 1
  have hCx : 0≤Cx := (schwartzEnvelopeConstant_pos Kx 1).le
  have hCy : 0≤Cy := (schwartzEnvelopeConstant_pos Ky 1).le
  have hki : Integrable (fun p : ℝ×ℝ =>
      normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p)
      (volume.prod volume) :=
    ((normalizedLineEnvelope_integrable cx rx hrx).mul_prod
      (normalizedLineEnvelope_integrable cy ry hry)).mul_bdd hUm.aestronglyMeasurable
        (Filter.Eventually.of_forall hUb)
  rw [show f w=f (w.1,w.2) from rfl,
    planar_vector_integral_reproduction Kx Ky f Rx Ry rx ry hrx hry hKx hKy hFx hFy w.1 w.2,
    ←integral_const_mul]
  apply norm_integral_le_of_norm_le (hki.const_mul (16*Cx*Cy))
  filter_upwards [] with p
  rw [norm_smul,norm_mul]
  have hx := scaledReproducingKernel_shifted_bound Kx rx cx w.1 p.1 hrx hw.1
  have hy := scaledReproducingKernel_shifted_bound Ky ry cy w.2 p.2 hry hw.2
  have hkx := normalizedLineEnvelope_nonneg cx rx p.1 hrx
  have hky := normalizedLineEnvelope_nonneg cy ry p.2 hry
  calc
    _ ≤ ((4*Cx)*normalizedLineEnvelope cx rx p.1)*
        ((4*Cy)*normalizedLineEnvelope cy ry p.2)*U p :=
      mul_le_mul (mul_le_mul hx hy (norm_nonneg _) (by positivity)) (hFU p)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- One exceptional set controls every packet and every evaluation
point of the box. -/
theorem planar_family_box_bound {ι : Type*}
    (Kx Ky : SchwartzMap ℝ ℂ) (F : ι → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (Rx Ry cx cy rx ry : ℝ) (hrx : 0<rx) (hry : 0<ry)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ a y ξ, 𝓕 (vectorHorizontalSlice (F a) y) ξ≠0 → |ξ|≤Rx/rx)
    (hFy : ∀ a x η, 𝓕 (vectorVerticalSlice (F a) x) η≠0 → |η|≤Ry/ry)
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ p, 0≤U p) (hUb : ∀ p, ‖U p‖≤B)
    (hFU : ∀ a p, ‖F a p‖≤U p) :
    ∀ᵐ z ∂volume.prod volume, z∈coordinateBox cx cy rx ry →
      ∀ a w, w∈coordinateBox cx cy rx ry →
        ‖F a w‖≤(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)*
          threeStrongMaximal U z := by
  have hC : 0≤16*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1 := by
    have := (schwartzEnvelopeConstant_pos Kx 1).le
    have := (schwartzEnvelopeConstant_pos Ky 1).le
    positivity
  filter_upwards [planar_kernel_le_strongMaximal hUm hU2 B hB hU0 hUb cx cy rx ry hrx hry] with z hz
  intro hzc a w hw
  calc
    _ ≤ (16*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)*
        ∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
          ∂volume.prod volume :=
      planar_reproduction_kernel_bound Kx Ky (F a) Rx Ry cx cy rx ry hrx hry hKx hKy
        (hFx a) (hFy a) U hUm B hUb (hFU a) w hw
    _ ≤ (16*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)*
        (9216*threeStrongMaximal U z) := mul_le_mul_of_nonneg_left (hz hzc) hC
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
