import OAI.Analysis.LipschitzHilbert.Packets.ShortPacketBoxes
import OAI.Analysis.LipschitzHilbert.Packets.BoxPacketVariation
import OAI.Analysis.LipschitzHilbert.Geometry.TransverseBoxDecay
import OAI.Analysis.LipschitzHilbert.Estimates.TileLatticeEnvelope

namespace OAI

/-! The fixed-box estimate for the actual short-packet fibers. Lattice
overlap, box location, and transverse decay are all discharged here. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem short_box_variation (hL : LepingleInput) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)]
      (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
      (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ × ℤ) (len : Fin N → ℝ)
      (a0 b0 u y r W C B : ℝ) (b : ℤ × ℤ),
      (∀ j, Function.Injective (site j)) → (∀ j, 0 < len j) → 0 < r → 0 < W →
      (∀ j i, X j i = a0 + len j * (site j i).1) →
      (∀ j i, Z j i = b0 + W * (site j i).2) →
      (∀ j i k x, ‖f j i k x‖ ≤ C *
        (lineEnvelope (X j i) (len j) 3 x * lineEnvelope (Z j i) W 2 y)) →
      (∑ j, len j * ∑ i : ShortBoxFiber len (centerBoxIndex X Z u y r W) r b j,
        ‖c j i‖ ^ 2) ≤ B * r →
      (∀ j i k ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (f j i k) ξ = 0) →
      (∀ j i k ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j i k) ξ = 0) →
      ENNReal.ofReal (((1 + |(b.1 : ℝ)|) ^ 2 / 8) ^ 2) *
        (∫⁻ x in Icc (u - r) (u + r), ENNReal.ofReal (finiteCubicVariation
          (fun n => hilbertPartialBandSum
            (fun j k => shortBoxSynthesis len (centerBoxIndex X Z u y r W) r
              (fun j i => c j i k) (fun j i => f j i k) b j) n x) N) ^ (2 / 3 : ℝ)) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ((4 * Real.pi) ^ 2 * C ^ 2 * 16 * Real.pi *
          (((1 + |(b.2 : ℝ)|) ^ 2 / 8) ^ 2)⁻¹ * (B * r)) := by
  obtain ⟨K,hK,hbound⟩ := box_packet_variation hL hlo hhi
  refine ⟨K,hK,?_⟩
  intro N κ ι instκ instι c f X Z site len a0 b0 u y r W C B b
    hinj hlen hr hW hX hZ henv hbudget hlow hhigh
  let index := centerBoxIndex X Z u y r W
  let fiber := fun j => ShortBoxFiber len index r b j
  have hcx (j : Fin N) (i : fiber j) : |X j i - (u + r * b.1)| ≤ r := by
    have h := packetBoxIndex_horizontal u y r W (X j i) (Z j i) hr
    change |X j i - (u + r * (index j i).1)| ≤ r at h
    rw [i.property.2] at h
    exact h
  have hcz (j : Fin N) (i : fiber j) : |Z j i - (y + W * b.2)| ≤ W := by
    have h := packetBoxIndex_vertical u y r W (X j i) (Z j i) hW
    change |Z j i - (y + W * (index j i).2)| ≤ W at h
    rw [i.property.2] at h
    exact h
  have hover (j : Fin N) (x : ℝ) :
      (∑ i : fiber j, lineEnvelope (Z j i) W 2 y * lineEnvelope (X j i) (len j) 3 x) ≤
        (4 * Real.pi) ^ 2 := by
    have h := injective_tile_lattice_overlap (fun i : fiber j => site j i)
      ((hinj j).comp Subtype.val_injective) a0 b0 (len j) W x y
      (hlen j).ne' hW.ne' (by norm_num : 1 ≤ (3 : ℕ)) (by norm_num : 1 ≤ (2 : ℕ))
    simpa only [hX, hZ, mul_comm] using h
  have hbudget' : (∑ j, len j * ∑ k, ∑ i : fiber j, ‖c j i k‖ ^ 2) ≤ B * r := by
    simpa only [component_coefficient_energy] using hbudget
  have h := hbound N κ (fun j _ => fiber j)
    (fun j k i => c j i k) (fun j k i => f j i k) (fun j _ i => X j i)
    (fun j _ i => lineEnvelope (Z j i) W 2 y) len u r b.1 C ((4 * Real.pi) ^ 2)
    ((((1 + |(b.2 : ℝ)|) ^ 2 / 8) ^ 2)⁻¹) B 1
    hlen hr (fun _ _ i => i.property.1)
    (fun _ _ _ => by unfold lineEnvelope; positivity)
    (fun j _ i => transverse_box_envelope (Z j i) y W b.2 2 hW (hcz j i))
    (fun j _ i => hcx j i) (by positivity) (by positivity)
    (fun j _ x => by simpa using hover j x)
    (fun j k i x => by simpa [mul_comm] using henv j i k x)
    hbudget' (fun j k i ξ hξ => hlow j i k ξ hξ) (fun j k i ξ hξ => hhigh j i k ξ hξ)
  simpa only [pow_one, shortBoxSynthesis, index, fiber] using h

end LipschitzHilbert

end

end OAI
