import OAI.Analysis.LipschitzHilbert.Trees.SourceBoxReproduction
import OAI.Analysis.LipschitzHilbert.Trees.SourceVectorSchwartz
import OAI.Analysis.LipschitzHilbert.Packets.PhysicalPlanarPacket

namespace OAI

/-! Removing each vertical bin carrier is an exact pointwise isometry.
Box reproduction can therefore use the narrow demodulated spectra. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
open DyadicLineGrid
variable {κ : Type*} [Fintype κ]

def verticalCarrier (nu : ℝ) (z : ℝ×ℝ) : ℂ := Complex.exp ((nu*z.2 : ℝ)*Complex.I)

theorem verticalCarrier_temperate (nu : ℝ) : Function.HasTemperateGrowth (verticalCarrier nu) := by
  change Function.HasTemperateGrowth (fun z : ℝ×ℝ => Complex.exp ((nu*z.2 : ℝ)*Complex.I))
  simpa only [sub_zero,zero_mul] using physicalPacketCarrier_temperate 0 0 0 nu

@[simp] theorem verticalCarrier_norm (nu : ℝ) (z : ℝ×ℝ) : ‖verticalCarrier nu z‖=1 := by
  simp [verticalCarrier,Complex.norm_exp]

def verticalDemodulation (nu : κ → ℝ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) :
    SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ) :=
  vectorSchwartz (fun k => SchwartzMap.smulLeftCLM ℂ (verticalCarrier (-nu k))
    (f.postcompCLM (vectorCoordinate k)))

@[simp] theorem verticalDemodulation_apply (nu : κ → ℝ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (z : ℝ×ℝ) (k : κ) :
    verticalDemodulation nu f z k=verticalCarrier (-nu k) z*f z k := by
  rw [verticalDemodulation,vectorSchwartz_apply,
    SchwartzMap.smulLeftCLM_apply_apply (verticalCarrier_temperate (-nu k))]
  rfl

@[simp] theorem verticalDemodulation_norm (nu : κ → ℝ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (z : ℝ×ℝ) :
    ‖verticalDemodulation nu f z‖=‖f z‖ := by
  have h : ‖verticalDemodulation nu f z‖^2=‖f z‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,verticalDemodulation_apply,norm_mul,
      verticalCarrier_norm,one_mul]
  nlinarith [norm_nonneg (verticalDemodulation nu f z),norm_nonneg (f z)]

def scalarVerticalDemodulation (nu : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (verticalCarrier (-nu)) f

@[simp] theorem scalarVerticalDemodulation_apply (nu : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    scalarVerticalDemodulation nu f z=verticalCarrier (-nu) z*f z := by
  exact SchwartzMap.smulLeftCLM_apply_apply (verticalCarrier_temperate (-nu)) f z

@[simp] theorem verticalDemodulation_zero (nu : κ → ℝ) :
    verticalDemodulation nu 0=0 := by
  ext z k
  simp

@[simp] theorem verticalDemodulation_sub (nu : κ → ℝ)
    (f g : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) :
    verticalDemodulation nu (f-g)=verticalDemodulation nu f-verticalDemodulation nu g := by
  ext z k
  simp [mul_sub]

@[simp] theorem verticalDemodulation_sum {J : Type*} (nu : κ → ℝ) (s : Finset J)
    (f : J → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) :
    verticalDemodulation nu (∑ j∈s, f j)=∑ j∈s, verticalDemodulation nu (f j) := by
  ext z k
  simp [sum_apply,WithLp.ofLp_sum,Finset.sum_apply,Finset.mul_sum]

/-- Uniform box control uses the demodulated supports, so its constants
are independent of the location of the individual vertical carriers. -/
theorem demodulated_family_box_bound {ι : Type*}
    (Kx Ky : SchwartzMap ℝ ℂ) (nu : κ → ℝ)
    (F : ι → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (Rx Ry cx cy rx ry : ℝ) (hrx : 0<rx) (hry : 0<ry)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ a y ξ, 𝓕 (vectorHorizontalSlice (verticalDemodulation nu (F a)) y) ξ≠0 → |ξ|≤Rx/rx)
    (hFy : ∀ a x η, 𝓕 (vectorVerticalSlice (verticalDemodulation nu (F a)) x) η≠0 → |η|≤Ry/ry)
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ p, 0≤U p) (hUb : ∀ p, ‖U p‖≤B)
    (hFU : ∀ a p, ‖F a p‖≤U p) :
    ∀ᵐ z ∂volume.prod volume, z∈coordinateBox cx cy rx ry →
      ∀ a w, w∈coordinateBox cx cy rx ry →
        ‖F a w‖≤(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)*
          threeStrongMaximal U z := by
  simpa only [verticalDemodulation_norm] using planar_family_box_bound Kx Ky
    (fun a => verticalDemodulation nu (F a)) Rx Ry cx cy rx ry hrx hry hKx hKy hFx hFy
    U hUm hU2 B hB hU0 hUb (by simpa only [verticalDemodulation_norm] using hFU)

end LipschitzHilbert

end

end OAI
