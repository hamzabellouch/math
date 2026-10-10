import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedBandForm

namespace OAI

/-! Enlarge the vertical reference width together with the auxiliary
angular precision. This leaves the physical multiplier and W/w unchanged. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

namespace AnnularPacketGeometry
variable {A B c C a M : ℝ}

def enlargeVertical (p : AnnularPacketGeometry A B c C a M) :
    AnnularPacketGeometry A (p.H*B) c C a M where
  H := p.H
  R := p.R+p.H*B
  hA := p.hA
  hB := mul_nonneg p.H_pos.le p.hB
  hc := p.hc
  hC := p.hC
  ha := p.ha
  hM := p.hM
  hH := p.hH
  hR := by linarith [p.hR,mul_nonneg p.H_pos.le p.hB]
  narrow := p.narrow
  size := by linarith [p.size,p.hB]
  radius := p.radius.trans (by linarith [mul_nonneg p.H_pos.le p.hB])
  quarter := p.quarter
  separation := p.separation
  coverage := p.coverage

end AnnularPacketGeometry

def verticallyRescaledWindow (beta : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0<H) : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow beta H⁻¹ (inv_ne_zero hH.ne')

theorem verticallyRescaledWindow_apply (beta : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0<H) (y : ℝ) :
    verticallyRescaledWindow beta H hH y=beta (y/H) := by
  rw [verticallyRescaledWindow,dilatedSlopeWindow_apply]
  congr 1
  ring

theorem verticallyRescaledWindow_symbolY (beta : SchwartzMap ℝ ℂ)
    (H W eta center : ℝ) (hH : 0<H) :
    verticallyRescaledWindow beta H hH (symbolY (H*W) eta center)=beta (symbolY W eta center) := by
  rw [verticallyRescaledWindow_apply]
  congr 1
  unfold symbolY
  field_simp

theorem verticallyRescaledWindow_support (beta : SchwartzMap ℝ ℂ)
    (B H : ℝ) (hH : 0<H) (hbeta : ∀ y, beta y≠0 → |y|≤B/2)
    (y : ℝ) (hy : verticallyRescaledWindow beta H hH y≠0) : |y|≤(H*B)/2 := by
  rw [verticallyRescaledWindow_apply] at hy
  have h := hbeta (y/H) hy
  rw [abs_div,abs_of_pos hH] at h
  have hh := (div_le_iff₀ hH).mp h
  nlinarith

theorem finitePartitionedBand_vertical_rescaling {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]
    (psi rho beta : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0<H)
    (topLength width w : ℝ) (labels : ∀ j, Finset (Label j))
    (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (u : ℝ×ℝ → ℝ) (f : κ → SchwartzMap (ℝ×ℝ) ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    finitePartitionedBand psi rho (verticallyRescaledWindow beta H hH) topLength (H*width) w
      labels theta center u f g=finitePartitionedBand psi rho beta topLength width w
        labels theta center u f g := by
  unfold finitePartitionedBand
  simp_rw [verticallyRescaledWindow_symbolY]

end LipschitzHilbert.PacketRepresentation

end

end OAI
