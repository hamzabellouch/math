import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenProfile
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalCoefficient

namespace OAI

/-! Only a nonzero frozen selector needs annular separation. Zero
selectors give zero packets, so empty scales and unused labels impose no
artificial spectral hypothesis. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

/-- Freezing a selector multiplies the original integral coefficient by
its complex conjugate. The assertion includes zero selectors. -/
theorem frozenProfile_mainCoefficient (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (u : ι j) (k : κ) :
    (P.frozenProfile c hc).family.mainCoefficient d v g j u k =
      conj (c j u k)*P.family.mainCoefficient d v g j u k := by
  have hsel (z : ℝ×ℝ) :
      (P.frozenProfile c hc).family.selectedWave d v ⟨j,u⟩ k z =
        c j u k*P.family.selectedWave d v ⟨j,u⟩ k z := by
    change (if v z ≤ d j then (P.frozenProfile c hc).raw 0 j u k z.1 z.2 else 0) =
      c j u k*(if v z ≤ d j then P.raw 0 j u k z.1 z.2 else 0)
    rw [P.frozenProfile_raw]
    by_cases h : v z ≤ d j <;> simp [h,smul_apply,smul_eq_mul]
  simp only [PlanarPacketFamily.mainCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change (↑(P.length j*P.width):ℂ)⁻¹*
      (∫ z, g z k*conj ((P.frozenProfile c hc).family.selectedWave d v ⟨j,u⟩ k z)) =
    conj (c j u k)*((↑(P.length j*P.width):ℂ)⁻¹*
      (∫ z, g z k*conj (P.family.selectedWave d v ⟨j,u⟩ k z)))
  have heq : (fun z => g z k*conj ((P.frozenProfile c hc).family.selectedWave d v ⟨j,u⟩ k z)) =
      (fun z => conj (c j u k)*(g z k*conj (P.family.selectedWave d v ⟨j,u⟩ k z))) := by
    funext z
    rw [hsel,map_mul]
    ring
  rw [heq,integral_const_mul]
  ring

/-- The same physical spectral wedge supplies the annuli of every
frozen raw jet. Separation is required precisely where the selector is
nonzero, rather than on all unused packet labels. -/
theorem frozenProfile_fourier_cutoffs (t w cStar cEta CEta cb Cb : ℝ)
    (hw : 0 < w) (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hspectrum : ∀ j u k xi eta, planarAngularFourier (P.physicalPacket t j u k) (xi,eta) ≠ 0 →
      |xi+(t+P.rowSlope j)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (hselector : ∀ j u k, c j u k ≠ 0 →
      cb*w/P.length j ≤ |P.rowSlope j| ∧ |P.rowSlope j| ≤ Cb*w/P.length j)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (∀ xi, |xi| < (((cEta*cb-cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val →
      𝓕 ((P.frozenProfile c hc).raw i j u k y) xi = 0) ∧
    (∀ xi, (((CEta*Cb+cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val < |xi| →
      𝓕 ((P.frozenProfile c hc).raw i j u k y) xi = 0) := by
  by_cases hz : c j u k = 0
  · rw [P.frozenProfile_raw,hz,zero_smul]
    simp
  have hsel : cb*w/P.length j ≤ |t-(t+P.rowSlope j)| ∧
      |t-(t+P.rowSlope j)| ≤ Cb*w/P.length j := by
    have heq : t-(t+P.rowSlope j) = -P.rowSlope j := by ring
    simpa only [heq,abs_neg] using hselector j u k hz
  have h := sourcePacket_jet_fourier_cutoffs (P.physicalPacket t j u k)
    y t (t+P.rowSlope j) (P.length j) w cStar cEta CEta cb Cb
    (P.length_pos j) hw hcEta hcb hCb (hspectrum j u k) hsel
    (P.frequency k) P.scale i
  have hraw : P.raw i j u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale i) y t :=
    P.raw_eq_physical_slice i j u k y t
  have heq (A : ℝ) : A/(2*Real.pi*P.length j) =
      ((A/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val := by
    rw [length,packet_annulus_dyadic_scale A P.topLength j.val P.topLength_pos.ne']
    ring
  rw [← hraw,heq,heq] at h
  constructor
  · intro xi hxi
    rw [P.frozenProfile_raw,fourier_smul,smul_apply,h.1 xi hxi,smul_zero]
  · intro xi hxi
    rw [P.frozenProfile_raw,fourier_smul,smul_apply,h.2 xi hxi,smul_zero]

end LipschitzHilbert.SourceLatticePacket

end

end OAI
