import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskedSynthesis
import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskedReference
import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskGeometry

namespace OAI

/-! Physical shortness and the narrow reference cone discharge the
mask-rate hypotheses. The resulting masked mixed moments use the
original integral coefficients and actual top masks. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem physicalReferenceMaskRate (P : SourceLatticePacket N κ ι)
    (T : ∀ j, ι j → SlopeBox) (L A t cone lo : ℝ) (hL : 0 < L)
    (hshort : ∀ j u, P.length j ≤ (T j u).length)
    (hcone : ∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j)
    (hsmall : (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone) ≤ min 1 (Real.pi*lo)) :
    ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j := by
  intro j u
  simpa only [one_mul,div_one] using
    ((T j u).scaled_maskLine_bounds L A t (P.length j) cone 1 lo
      hL (P.length_pos j) zero_lt_one (hshort j u) (hcone j u) hsmall).1

/-- All constants precede the finite packet family, masks, and root
window. No derivative or Fourier premise is imposed on the masks. -/
theorem masked_mixed_reference_uniform_moments (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ B M : ℝ, 0 < B ∧ 0 < M ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      ∀ (T : ∀ j, ι j → SlopeBox) (L A t cone : ℝ) (hL : 0 < L)
        (hshort : ∀ j u, P.length j ≤ (T j u).length)
        (hcone : ∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j)
        (hsmall : (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone) ≤ min 1 (Real.pi*lo))
        (y : ℝ) (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) → ∀ p : ℝ, 0 ≤ p →
      let rate := P.physicalReferenceMaskRate T L A t cone lo hL hshort hcone hsmall
      let Q := P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y rate
      (∫⁻ x, (ENNReal.ofReal |Q.squareFunction x|)^p ∂grid.lineMeasure) ≤
        referenceSquareMomentCost B grid p*grid.lineMeasure univ ∧
      (∫⁻ x, (ENNReal.ofReal |Q.variation x|)^p ∂grid.lineMeasure) ≤
        referenceVariationMomentCost M (2*P.constant) B grid p*grid.lineMeasure univ := by
  obtain ⟨B,hB,hbudget⟩ := referenceAnalyzedLine_uniform_budget hVariation hlo hhi
  obtain ⟨M,hM,hmoment⟩ := LinePacketFamily.sinc_masked_uniform_moments hVariation hlo hhi
  refine ⟨B/Real.pi^4,M,by positivity,hM,?_⟩
  intro N κ ι _ _ P c hc alt hAlt d v hv g hg hg1 hd hAlow hAhigh hSlow hShigh
    T L A t cone hL hshort hcone hsmall y grid hb hwidth p hp
  let Q := P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y
  have hB0 : 0 ≤ B/Real.pi^4 := by positivity
  have hQ : Q.HasLocalBudget (B/Real.pi^4) :=
    hbudget N κ ι (P.frozenProfile c hc) d v hv g hg hg1 hd hAlow hAhigh y
  obtain ⟨hl,hh⟩ := (P.withProfile alt hAlt).referencePlanarFamily_cutoffs hSlow hShigh
  have hrate : ∀ j u (_k : κ), 2*(⌈L⌉₊:ℝ)*
      (|P.topLength*(T j u).maskLineA L A|+|P.topLength*(T j u).maskLineC L A t|) ≤
      1/Q.length j := by
    intro j u k
    rw [P.mixedReferenceLine_length c hc alt hAlt d v hv g hg hg1]
    exact ((T j u).scaled_maskLine_bounds L A t (P.length j) cone P.topLength lo
      hL (P.length_pos j) P.topLength_pos (hshort j u) (hcone j u) hsmall).1
  have hband : ∀ j u (_k : κ), (2*(⌈L⌉₊:ℝ))*
      ((|P.topLength*(T j u).maskLineA L A|+
        |P.topLength*(T j u).maskLineC L A t|)/(2*Real.pi)) ≤
      (lo/2)*(2:ℝ)^j.val := by
    intro j u k
    have h := ((T j u).scaled_maskLine_bounds L A t (P.length j) cone P.topLength lo
      hL (P.length_pos j) P.topLength_pos (hshort j u) (hcone j u) hsmall).2
    convert h using 1
    rw [length]
    field_simp [P.topLength_pos.ne']
  have hwidth' : ∀ j (_u : ι j), Q.length j ≤ grid.width := by
    intro j u
    rw [P.mixedReferenceLine_length c hc alt hAlt d v hv g hg hg1]
    exact (div_le_iff₀ P.topLength_pos).mpr (by simpa only [mul_comm] using hwidth j u)
  exact hmoment N κ ι Q (B/Real.pi^4) hB0 hQ
    (fun j u k xi hxi => hl j u k y xi hxi)
    (fun j u k xi hxi => hh j u k y xi hxi) ⌈L⌉₊
    (fun j u _ => P.topLength*(T j u).maskLineA L A)
    (fun j u _ => (T j u).maskLineB L A)
    (fun j u _ => P.topLength*(T j u).maskLineC L A t)
    (fun j u _ => (T j u).maskLineD L A y) hrate hband grid hb hwidth' p hp

end LipschitzHilbert.SourceLatticePacket

end

end OAI
