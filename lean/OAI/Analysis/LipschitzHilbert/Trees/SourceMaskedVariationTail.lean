import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskedPhysicalTail
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalTail

namespace OAI

/-! The masked reference variation tail in original physical variables.
The interval may have any origin and any positive length containing the
retained packet lengths. Neither its scale nor its origin enters the
relative exceptional-measure constant. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ)

def physicalMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ u : ι j,
    (conj (c j u k)*P.physicalCoefficient t d v g j u k)*
      ((T j u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j u k (x,y+t*x))

def physicalMaskedVariation (x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum (fun j => P.physicalMaskedBand c alt hAlt d v g T L A t y j x)) N

variable (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

theorem physicalMaskedBand_eq_reference (j : Fin N) (x : ℝ) :
    P.physicalMaskedBand c alt hAlt d v g T L A t y j x =
      P.maskedMixedReferenceBand c hc alt hAlt d
        (fun z => v (sourceReferenceToPhysical t z))
        (fun z => g (sourceReferenceToPhysical t z)) T L A t y j x :=
  (P.maskedMixedReferenceBand_physical c hc alt hAlt d v g T L A t y j x).symm

theorem physicalMaskedVariation_normalization
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (rate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j)
    (x : ℝ) :
    P.physicalMaskedVariation c alt hAlt d v g T L A t y (P.topLength*x) =
      (P.constant*Real.pi^2)*
      (P.maskedMixedReferenceLine c hc alt hAlt d
        (fun z => v (sourceReferenceToPhysical t z))
        (hv.comp (sourceReferenceToPhysical t).measurable)
        (fun z => g (sourceReferenceToPhysical t z))
        (hg.comp (sourceReferenceToPhysical t).measurable)
        (fun z => hg1 (sourceReferenceToPhysical t z)) T L A t y rate).variation x := by
  unfold physicalMaskedVariation
  simp_rw [P.physicalMaskedBand_eq_reference c alt hAlt d v g T L A t y hc]
  exact P.maskedMixedReferenceBand_variation c hc alt hAlt d _
    (hv.comp (sourceReferenceToPhysical t).measurable) _
    (hg.comp (sourceReferenceToPhysical t).measurable)
    (fun z => hg1 (sourceReferenceToPhysical t z)) T L A t y rate x

include hc in
theorem physicalMaskedVariation_continuous
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (rate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j) :
    Continuous (P.physicalMaskedVariation c alt hAlt d v g T L A t y) := by
  let Q := P.maskedMixedReferenceLine c hc alt hAlt d
    (fun z => v (sourceReferenceToPhysical t z))
    (hv.comp (sourceReferenceToPhysical t).measurable)
    (fun z => g (sourceReferenceToPhysical t z))
    (hg.comp (sourceReferenceToPhysical t).measurable)
    (fun z => hg1 (sourceReferenceToPhysical t z)) T L A t y rate
  have heq : P.physicalMaskedVariation c alt hAlt d v g T L A t y =
      fun x => (P.constant*Real.pi^2)*Q.variation (x/P.topLength) := by
    funext x
    have h := P.physicalMaskedVariation_normalization c alt hAlt d v g T L A t y hc
      hv hg hg1 rate (x/P.topLength)
    simpa only [mul_div_cancel₀ _ P.topLength_pos.ne'] using h
  rw [heq]
  exact continuous_const.mul (Q.continuous_variation.comp (continuous_id.div_const P.topLength))

/-- The actual physical masked variation has an arbitrary exponential
tail at a fixed polynomial threshold, uniformly over packet and interval
scales. The exceptional event is measurable by the exact normalization. -/
theorem physical_masked_variation_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^q →
    ∀ (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
    ∀ (T : ∀ j, ι j → SlopeBox) (t : ℝ),
      (∀ j u, P.length j ≤ (T j u).length) →
      (∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (_i : ι j), P.length j ≤ H) →
      Measurable (P.physicalMaskedVariation c alt hAlt d v g T L A t y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+6) ≤ |P.physicalMaskedVariation c alt hAlt d v g T L A t y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [masked_mixed_reference_polynomial_tails hVariation hlo hhi q J A cone hq hJ hA hcone,
    eventually_ge_atTop (max 1 (Real.pi^2))] with L htail hlarge
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL : 0 < L := zero_lt_one.trans_le hL1
  intro N κ ι _ _ P hP c hc alt hAlt d v hv g hg hg1 hd hAlow hAhigh hSlow hShigh
    T t hshort hcone' y u H hH hwidth
  have hv' := hv.comp (sourceReferenceToPhysical t).measurable
  have hg' := hg.comp (sourceReferenceToPhysical t).measurable
  obtain ⟨rate,htail⟩ := htail N κ ι P hP c hc alt hAlt d _ hv' _ hg'
    (fun z => hg1 (sourceReferenceToPhysical t z)) hd hAlow hAhigh hSlow hShigh T t hshort hcone'
  let Q := P.maskedMixedReferenceLine c hc alt hAlt d _ hv' _ hg'
    (fun z => hg1 (sourceReferenceToPhysical t z)) T L A t y rate
  let grid : FiniteLineGrid :=
    { branching := 2, branching_pos := by decide, origin := u/P.topLength,
      width := H/P.topLength, width_pos := div_pos hH P.topLength_pos, depth := 0 }
  have hwidth' : ∀ j (_i : ι j), P.length j ≤ P.topLength*grid.width := by
    intro j i
    simpa only [grid,mul_div_cancel₀ _ P.topLength_pos.ne'] using hwidth j i
  have ht := (htail y grid rfl hwidth').2
  have hmass : grid.lineMeasure univ = ENNReal.ofReal (H/P.topLength) := by
    change (volume.restrict (Ico (u/P.topLength) (u/P.topLength+H/P.topLength))) univ = _
    rw [Measure.restrict_apply_univ,Real.volume_Ico]
    congr 1
    ring
  rw [hmass] at ht
  have hcont := P.physicalMaskedVariation_continuous c alt hAlt d v g T L A t y hc hv hg hg1 rate
  refine ⟨hcont.measurable,?_⟩
  have hthreshold : (P.constant*Real.pi^2)*L^(q+5) ≤ L^(2*q+6) := by
    calc
      _ ≤ (L^q*L)*L^(q+5) := mul_le_mul_of_nonneg_right
        (mul_le_mul hP ((le_max_right _ _).trans hlarge) (sq_nonneg _)
          (Real.rpow_nonneg hL.le _)) (Real.rpow_nonneg hL.le _)
      _ = (L^q*L^(1:ℝ))*L^(q+5) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hL,← Real.rpow_add hL]
        congr 1
        ring
  have h := source_physical_tail P.topLength (P.constant*Real.pi^2)
    (u/P.topLength) (H/P.topLength) (Real.exp (-J*L)) (L^(q+5)) (L^(2*q+6))
    P.topLength_pos (mul_pos P.constant_pos (pow_pos Real.pi_pos _))
    (P.physicalMaskedVariation c alt hAlt d v g T L A t y) Q.variation hcont.measurable
    (fun x => P.physicalMaskedVariation_normalization c alt hAlt d v g T L A t y hc
      hv hg hg1 rate x) hthreshold ht
  have hlo' : P.topLength*(u/P.topLength) = u := mul_div_cancel₀ _ P.topLength_pos.ne'
  have hhi' : P.topLength*(u/P.topLength+H/P.topLength) = u+H := by
    rw [mul_add,mul_div_cancel₀ _ P.topLength_pos.ne',mul_div_cancel₀ _ P.topLength_pos.ne']
  have hlen : P.topLength*(H/P.topLength) = H := mul_div_cancel₀ _ P.topLength_pos.ne'
  rwa [hlo',hhi',hlen] at h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
