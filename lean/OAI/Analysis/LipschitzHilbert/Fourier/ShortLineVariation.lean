import OAI.Analysis.LipschitzHilbert.Estimates.ShortBoxEstimate
import OAI.Analysis.LipschitzHilbert.Estimates.BoxVariationWeights
import OAI.Analysis.LipschitzHilbert.Packets.HilbertPacketLinearity

namespace OAI

/-! Summing the actual short-scale packet boxes on one reference interval. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem short_line_variation (hL : LepingleInput) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)]
      (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
      (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ × ℤ) (len : Fin N → ℝ)
      (a0 b0 u y r W C B : ℝ),
      (∀ j, Function.Injective (site j)) → (∀ j, 0 < len j) → 0 < r → 0 < W → 0 ≤ B →
      (∀ j i, X j i = a0 + len j * (site j i).1) →
      (∀ j i, Z j i = b0 + W * (site j i).2) →
      (∀ j i k x, ‖f j i k x‖ ≤ C *
        (lineEnvelope (X j i) (len j) 3 x * lineEnvelope (Z j i) W 2 y)) →
      (∀ b : ℤ × ℤ, (∑ j, len j *
        ∑ i : ShortBoxFiber len (centerBoxIndex X Z u y r W) r b j, ‖c j i‖ ^ 2) ≤ B * r) →
      (∀ j i k ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (f j i k) ξ = 0) →
      (∀ j i k ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j i k) ξ = 0) →
      (∫⁻ x in Icc (u - r) (u + r), ENNReal.ofReal (finiteCubicVariation
        (fun n => hilbertPartialBandSum
          (fun j k => if len j ≤ r then packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0)
          n x) N) ^ (2 / 3 : ℝ)) ≤ ENNReal.ofReal (A * C ^ 2 * B * r) := by
  obtain ⟨K,hK,hbox⟩ := short_box_variation hL hlo hhi
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  let A : ℝ := (4 * Real.pi) ^ 4 * 4096 * ((K : ℝ) * (4 * Real.pi) ^ 2 * 16 * Real.pi)
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro N κ ι instκ instι c f X Z site len a0 b0 u y r W C B
    hinj hlen hr hW hB hX hZ henv hbudget hlow hhigh
  let index := centerBoxIndex X Z u y r W
  let boxes := allPacketBoxes index
  let G := fun (b : {b // b ∈ boxes}) j k =>
    shortBoxSynthesis len index r (fun j i => c j i k) (fun j i => f j i k) b j
  let F := fun (b : {b // b ∈ boxes}) n x => hilbertPartialBandSum (G b) n x
  let M : ℝ := (K : ℝ) * (4 * Real.pi) ^ 2 * C ^ 2 * 16 * Real.pi * (B * r)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hF (b : {b // b ∈ boxes}) (n : ℕ) : Measurable (F b n) :=
    (hilbertPartialBandSum_continuous (G b) n).measurable
  have hbox' (b : {b // b ∈ boxes}) :
      ENNReal.ofReal (((1 + |(b.val.1 : ℝ)|) ^ 2 / 8) ^ 2) *
        (∫⁻ x in Icc (u - r) (u + r), ENNReal.ofReal
          (finiteCubicVariation (fun n => F b n x) N) ^ (2 / 3 : ℝ)) ≤
        ENNReal.ofReal (M * (((1 + |(b.val.2 : ℝ)|) ^ 2 / 8) ^ 2)⁻¹) := by
    have h := hbox N κ ι c f X Z site len a0 b0 u y r W C B b
      hinj hlen hr hW hX hZ henv (hbudget b) hlow hhigh
    apply h.trans_eq
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
    congr 1
    dsimp [M]
    ring
  have hsum (n : ℕ) (x : ℝ) :
      hilbertPartialBandSum
        (fun j k => if len j ≤ r then packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n x =
      ∑ b : {b // b ∈ boxes}, F b n x := by
    have hs (j : Fin N) (k : κ) :
        (if len j ≤ r then packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) =
          ∑ b : {b // b ∈ boxes}, G b j k := by
      rw [shortSynthesis_eq_sum_boxes len index r (fun j i => c j i k) (fun j i => f j i k) j]
      exact Finset.sum_subtype boxes (fun _ => Iff.rfl) _
    simp_rw [hs]
    exact hilbertPartialBandSum_finset_sum Finset.univ G n x
  have h := lintegral_sum_box_variation (volume.restrict (Icc (u - r) (u + r)))
    F hF N Subtype.val Subtype.val_injective hM hbox'
  simp_rw [hsum]
  apply h.trans_eq
  congr 1
  dsimp [A, M]
  ring

end LipschitzHilbert

end

end OAI
