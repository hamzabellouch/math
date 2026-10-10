import OAI.Analysis.LipschitzHilbert.Estimates.EnvelopeSynthesis
import OAI.Analysis.LipschitzHilbert.Estimates.TileLatticeEnvelope

namespace OAI

/-! Polynomially localized packet synthesis energy with arbitrary dual
coefficients. No local coefficient budget is assumed here. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem weighted_component_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (rho : ι → ℝ) :
    (∑ k, ∑ i, ‖c i k‖ ^ 2 * rho i) = ∑ i, ‖c i‖ ^ 2 * rho i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq]

theorem weighted_packet_energy {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ × ℤ) (len : Fin N → ℝ)
    (a0 b0 a r W y C : ℝ) (hr : 0 < r) (hW : 0 < W)
    (hlen : ∀ j, 0 < len j) (hlenr : ∀ j, ∀ _ : ι j, len j ≤ r)
    (hinj : ∀ j, Function.Injective (site j))
    (hX : ∀ j i, X j i = a0+len j*(site j i).1)
    (hZ : ∀ j i, Z j i = b0+W*(site j i).2)
    (hcenter : ∀ j i, |X j i-a| ≤ r)
    (hf : ∀ j i k x, ‖f j i k x‖ ≤ C *
      (lineEnvelope (X j i) (len j) 3 x * lineEnvelope (Z j i) W 3 y)) :
    (∑ j, ∑ k, ∫ x, ‖polynomialLocalization a r 1
      (packetSynthesis (fun i => c j i k) (fun i => f j i k)) x‖ ^ 2) ≤
      ((4 * Real.pi)^2 * C^2 * 16 * Real.pi) *
        ∑ j, len j * ∑ i, ‖c j i‖ ^ 2 * lineEnvelope (Z j i) W 3 y := by
  let D := (4 * Real.pi)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hscalar (j : Fin N) (k : κ) :
      (∫ x, ‖polynomialLocalization a r 1
        (packetSynthesis (fun i => c j i k) (fun i => f j i k)) x‖ ^ 2) ≤
        (D * C^2 * 16 * Real.pi) * len j *
          ∑ i, ‖c j i k‖ ^ 2 * lineEnvelope (Z j i) W 3 y := by
    classical
    by_cases hj : Nonempty (ι j)
    swap
    · let : IsEmpty (ι j) := ⟨fun i => hj ⟨i⟩⟩
      simp [packetSynthesis, polynomialLocalization_apply]
    have hrho (i : ι j) : 0 < lineEnvelope (Z j i) W 3 y := by unfold lineEnvelope; positivity
    have hover (x : ℝ) : (∑ i, lineEnvelope (Z j i) W 3 y * lineEnvelope (X j i) (len j) 3 x) ≤ D := by
      simp_rw [hX,hZ]
      simpa only [D, mul_comm] using injective_tile_lattice_overlap (site j) (hinj j)
        a0 b0 (len j) W x y (hlen j).ne' hW.ne' (by decide : 1 ≤ 3) (by decide : 1 ≤ 3)
    have h := polynomial_packetSynthesis_energy (fun i => c j i k) (fun i => f j i k)
      (X j) (fun i => lineEnvelope (Z j i) W 3 y) a (len j) r C D 1
      (hlen j) hr (hlenr j (Classical.choice hj)) hrho (hcenter j) hD hover
      (fun i x => by simpa only [show 1 + 1 * 2 = (3 : ℕ) from rfl, mul_comm] using hf j i k x)
    convert h using 1
    ring
  calc
    _ ≤ ∑ j, ∑ k, (D * C^2 * 16 * Real.pi) * len j *
        ∑ i, ‖c j i k‖ ^ 2 * lineEnvelope (Z j i) W 3 y :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hscalar j k))
    _ = _ := by
      simp_rw [← Finset.mul_sum, weighted_component_energy]
      simp only [D, ← Finset.mul_sum, mul_assoc]

end LipschitzHilbert

end

end OAI
