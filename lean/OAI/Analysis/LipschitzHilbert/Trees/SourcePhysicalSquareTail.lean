import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalReferenceSquare
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceThreshold
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalTail

namespace OAI

/-! The positive main square has a tail on every original physical
interval, with the exact reference coordinate change and no interval
scale in its constants. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

 theorem physical_reference_square_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (q J : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^q →
    ∀ (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j u k y) xi = 0) →
    ∀ (t y u H : ℝ), 0 < H → (∀ j (_i : ι j), P.length j ≤ H) →
      Measurable (P.physicalReferenceSquare t d v hv g hg hg1 y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(q+4) ≤ |P.physicalReferenceSquare t d v hv g hg hg1 y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  obtain ⟨B,M,hB,hM,hm⟩ := reference_uniform_moments hVariation hlo hhi
  have hB0 : 0 ≤ B/Real.pi^4 := by positivity
  filter_upwards [eventually_reference_thresholds M (B/Real.pi^4) q J hM.le hB0 hq hJ]
    with L hthreshold
  obtain ⟨n,hn,hdecay,hT,hthreshold⟩ := hthreshold
  intro N κ ι _ _ P hP d v hv g hg hg1 hd hlow hhigh t y u H hH hwidth
  let Q := P.physicalReferenceLine t d v hv g hg hg1 y
  let grid : FiniteLineGrid :=
    { branching := 2, branching_pos := by decide, origin := u/P.topLength,
      width := H/P.topLength, width_pos := div_pos hH P.topLength_pos, depth := 0 }
  have hv' := hv.comp (sourceReferenceToPhysical t).measurable
  have hg' := hg.comp (sourceReferenceToPhysical t).measurable
  have hwidth' : ∀ j (_i : ι j), P.length j ≤ P.topLength*grid.width := by
    intro j i
    simpa only [grid,mul_div_cancel₀ _ P.topLength_pos.ne'] using hwidth j i
  have hmoment := hm N κ ι P d _ hv' _ hg'
    (fun z => hg1 (sourceReferenceToPhysical t z)) hd hlow hhigh y grid (by decide : 1 < 2)
    hwidth'
  have ht := hthreshold grid P.constant rfl P.constant_pos.le hP
  have htail := (reference_polynomial_tails_of_moments grid.lineMeasure Q.squareFunction Q.variation
    (Q.squareSum_continuous.sqrt.measurable) Q.continuous_variation.measurable
    M (B/Real.pi^4) P.constant (L^(q+4)) grid hB0 P.constant_pos.le n hn hT ht.1 ht.2
    (hmoment (2*(n:ℝ)) (by positivity)).1 (hmoment n (by positivity)).2).1
  have hdecay' : (1/4:ℝ≥0∞)^n ≤ ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal hdecay
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4)] at h
    norm_num only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat] at h
    simpa using h
  have hmass : grid.lineMeasure univ = ENNReal.ofReal (H/P.topLength) := by
    change (volume.restrict (Ico (u/P.topLength) (u/P.topLength+H/P.topLength))) univ = _
    rw [Measure.restrict_apply_univ,Real.volume_Ico]
    congr 1
    ring
  have htail' := htail.trans (mul_le_mul' hdecay' le_rfl)
  rw [hmass] at htail'
  have hmeas : Measurable (P.physicalReferenceSquare t d v hv g hg hg1 y) :=
    Q.squareSum_continuous.sqrt.measurable.comp (measurable_id.div_const P.topLength)
  refine ⟨hmeas,?_⟩
  have h := source_physical_tail P.topLength 1 (u/P.topLength) (H/P.topLength)
    (Real.exp (-J*L)) (L^(q+4)) (L^(q+4)) P.topLength_pos zero_lt_one
    (P.physicalReferenceSquare t d v hv g hg hg1 y) Q.squareFunction hmeas
    (fun x => by
      change Q.squareFunction ((P.topLength*x)/P.topLength) = 1*Q.squareFunction x
      rw [mul_div_cancel_left₀ _ P.topLength_pos.ne',one_mul])
    (by simp only [one_mul,le_refl]) htail'
  have hlo' : P.topLength*(u/P.topLength) = u := mul_div_cancel₀ _ P.topLength_pos.ne'
  have hhi' : P.topLength*(u/P.topLength+H/P.topLength) = u+H := by
    rw [mul_add,mul_div_cancel₀ _ P.topLength_pos.ne',mul_div_cancel₀ _ P.topLength_pos.ne']
  have hlen : P.topLength*(H/P.topLength) = H := mul_div_cancel₀ _ P.topLength_pos.ne'
  rwa [hlo',hhi',hlen] at h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
