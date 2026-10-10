import OAI.Analysis.LipschitzHilbert.Estimates.TotalBinError
import OAI.Analysis.LipschitzHilbert.Estimates.BinErrorParameters

namespace OAI

/-! Substitution of the manuscript's actual bin count and width into the
total commutator error, followed by its small-time decay. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

def totalBinErrorCoefficient (k : SchwartzMap ℝ ℂ) (C : ℝ) : ℝ :=
  (2*C+3)*(4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant verticalBinProfile*C^2)

theorem totalBinErrorCoefficient_nonneg (k : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0<C) :
    0≤totalBinErrorCoefficient k C := by
  unfold totalBinErrorCoefficient
  exact mul_nonneg (by linarith) (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (verticalProfileCommutatorConstant_nonneg _)) (sq_nonneg _))

def totalProjectedBinError (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength w W c C : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  ∑ n : verticalBinLabels ⌈C*W/w⌉₊ w W c C,
    finiteBinError k verticalBinProfile N topLength W (verticalBinCenter ⌈C*W/w⌉₊ W n) u
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter ⌈C*W/w⌉₊ W n) f) z

theorem totalProjectedBinError_energy (k : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength w W c C m : ℝ) (htop : 0<topLength) (hw : 0<w) (hW : 0<W)
    (hC : 0<C) (hm : 1≤m) (hWm : W=m*w)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤C/w) :
    MemLp (totalProjectedBinError k N topLength w W c C u f) 2 planeMeasure ∧
      (∫ z, ‖totalProjectedBinError k N topLength w W c C u f z‖^2 ∂planeMeasure)≤
        totalBinErrorCoefficient k C*m^3*topLength^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  let I := verticalBinLabels ⌈C*W/w⌉₊ w W c C
  have hI : I⊆Finset.range (2*⌈C*W/w⌉₊+1) := Finset.filter_subset _ _
  obtain ⟨hmem,he⟩ := totalBinError_energy k N ⌈C*W/w⌉₊ I hI topLength W htop hW
    u hu f (C/w) (by positivity) hband
  refine ⟨hmem,he.trans ?_⟩
  have hquot : C*W/w=C*m := by rw [hWm]; field_simp
  have hcard : (I.card:ℝ)≤(2*C+3)*m := by
    have hc := verticalBinLabels_card w W c C hw hW hC.le
    have hc' : (I.card:ℝ)≤2*(C*m)+3 := by
      calc
        _ ≤ 2*(C*W/w)+3 := hc
        _ = _ := by rw [hquot]
    nlinarith
  have hfreq : topLength*W*(C/w)=topLength*m*C := by rw [hWm]; field_simp
  have hnonneg : 0≤4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant verticalBinProfile*
      (topLength*W*(C/w))^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (verticalProfileCommutatorConstant_nonneg _)) (sq_nonneg _)
  calc
    _ ≤ ((2*C+3)*m)*(4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant verticalBinProfile*
        (topLength*W*(C/w))^2)*(∫ z, ‖f z‖^2 ∂planeMeasure) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hnonneg)
        (integral_nonneg fun _ => sq_nonneg _)
    _ = _ := by rw [hfreq]; unfold totalBinErrorCoefficient; ring

theorem eventually_totalProjectedBinError (k : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0<C) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (topLength w W c m : ℝ),
      0<topLength → 0<w → 0<W → 1≤m → W=m*w →
      m≤2*Real.exp (L^(9/10:ℝ)) → topLength≤Real.exp (-(L^(97/100:ℝ))) →
    ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u → ∀ (f : SchwartzMap (ℝ×ℝ) ℂ),
      (∀ omega, planarFourier f omega≠0 → |omega.2|≤C/w) →
      (∫ z, ‖totalProjectedBinError k N topLength w W c C u f z‖^2 ∂planeMeasure)≤
        L^(-40:ℝ)*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  filter_upwards [eventually_cubic_width_short_time (totalBinErrorCoefficient k C)
    (totalBinErrorCoefficient_nonneg k C hC)] with L hdec
  intro N topLength w W c m htop hw hW hm hWm hmb htb u hu f hband
  exact (totalProjectedBinError_energy k N topLength w W c C m htop hw hW hC hm hWm
    u hu f hband).2.trans (mul_le_mul_of_nonneg_right
      (hdec m topLength (by linarith) hmb htop.le htb) (integral_nonneg fun _ => sq_nonneg _))

end LipschitzHilbert.PacketRepresentation

end

end OAI
