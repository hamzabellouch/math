import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceMoments
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedMoments
import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenSpectrum

namespace OAI

/-! Square and cubic-variation moments for the actual normalized
reference collection. Its root window need only contain retained
lengths, so the short-packet restriction introduces no larger window. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

def referenceSquareMomentCost (B : ℝ) (grid : FiniteLineGrid) (p : ℝ) : ℝ≥0∞ :=
  (2:ℝ≥0∞)^(p/2)*(7*ENNReal.ofReal (((p/2)*(((grid.branching:ℝ)+2)*
    (2*LinePacketFamily.squareMeanConstant B+48*(4*Real.pi)^4))/Real.log (3/2))^(p/2))+
    (ENNReal.ofReal (LinePacketFamily.squareMeanConstant B))^(p/2))

def referenceVariationMomentCost (M C B : ℝ) (grid : FiniteLineGrid) (p : ℝ) : ℝ≥0∞ :=
  (2:ℝ≥0∞)^p*(7*ENNReal.ofReal ((p*(((grid.branching:ℝ)+2)*
    (2*Real.sqrt (M*C^2*B+1)+4*(C*(4*Real.pi)^2)))/Real.log (3/2))^p)+
    (ENNReal.ofReal (Real.sqrt (M*C^2*B+1)))^p)

/-- Both constants precede all finite index types and the horizontal
scale. The spectra are the concrete annuli proved from original packet
spectra by `frozenProfile_fourier_cutoffs`. -/
theorem reference_uniform_moments (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A M : ℝ, 0 < A ∧ 0 < M ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j u k y) xi = 0) →
      ∀ (y : ℝ) (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) → ∀ p : ℝ, 0 ≤ p →
      let Q := P.referenceAnalyzedLine d v hv g hg hg1 y
      (∫⁻ x, (ENNReal.ofReal |Q.squareFunction x|)^p ∂grid.lineMeasure) ≤
        referenceSquareMomentCost (A/Real.pi^4) grid p*grid.lineMeasure univ ∧
      (∫⁻ x, (ENNReal.ofReal |Q.variation x|)^p ∂grid.lineMeasure) ≤
        referenceVariationMomentCost M P.constant (A/Real.pi^4) grid p*grid.lineMeasure univ := by
  obtain ⟨A,hA,hbudget⟩ := referenceAnalyzedLine_uniform_budget hL hlo hhi
  obtain ⟨M,hM,hvariation⟩ := LinePacketFamily.uniform_line_moment_of_supported hL hlo hhi
  refine ⟨A,M,hA,hM,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 hd hlow hhigh y grid hb hwidth p hp
  let Q := P.referenceAnalyzedLine d v hv g hg hg1 y
  have hB : 0 ≤ A/Real.pi^4 := div_nonneg hA.le (pow_nonneg Real.pi_pos.le _)
  have hQ := hbudget N κ ι P d v hv g hg hg1 hd hlow hhigh y
  have hlen (j : Fin N) : Q.length j = P.length j/P.topLength := by
    change (P.topLength/P.topLength)/(2:ℝ)^j.val = (P.topLength/(2:ℝ)^j.val)/P.topLength
    ring
  have hwidth' (j : Fin N) (u : ι j) : Q.length j ≤ grid.width := by
    rw [hlen]
    exact (div_le_iff₀ P.topLength_pos).mpr (by simpa only [mul_comm] using hwidth j u)
  obtain ⟨hl,hh⟩ := P.referencePlanarFamily_cutoffs hlow hhigh
  refine ⟨?_,?_⟩
  · exact Q.squareFunction_moment_of_supported grid hb hwidth' hB hQ hp
  · exact hvariation N κ ι Q (A/Real.pi^4) hB hQ
      (fun j u k xi hxi => hl j u k y xi hxi)
      (fun j u k xi hxi => hh j u k y xi hxi) grid hb hwidth' p hp

/-- Active frozen selector values give the required normalized spectra
from just the original physical packet spectrum. -/
theorem frozen_reference_spectral_inputs {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
    (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
    (t w cStar cEta CEta cb Cb : ℝ)
    (hw : 0 < w) (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hspectrum : ∀ j u k xi eta, planarAngularFourier (P.physicalPacket t j u k) (xi,eta) ≠ 0 →
      |xi+(t+P.rowSlope j)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (hselector : ∀ j u k, c j u k ≠ 0 →
      cb*w/P.length j ≤ |P.rowSlope j| ∧ |P.rowSlope j| ≤ Cb*w/P.length j) :
    (∀ j u k y xi,
      |xi| < (((cEta*cb-cStar)/(2*Real.pi))/(P.frozenProfile c hc).topLength)*(2:ℝ)^j.val →
      𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) ∧
    (∀ j u k y xi,
      (((CEta*Cb+cStar)/(2*Real.pi))/(P.frozenProfile c hc).topLength)*(2:ℝ)^j.val < |xi| →
      𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) := by
  exact ⟨fun j u k y => (P.frozenProfile_fourier_cutoffs c hc t w cStar cEta CEta cb Cb
    hw hcEta hcb hCb hspectrum hselector 0 j u k y).1,
    fun j u k y => (P.frozenProfile_fourier_cutoffs c hc t w cStar cEta CEta cb Cb
    hw hcEta hcb hCb hspectrum hselector 0 j u k y).2⟩

end LipschitzHilbert.SourceLatticePacket

end

end OAI
