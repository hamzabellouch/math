import OAI.Combinatorics.Progressions.Linear.ShiftFailurePositiveBasis

namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open scoped BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_partner_anchor {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
    (B : PositiveShiftBasis s N q a J) (H : Finset (ZMod N))
    (hH : H.Nonempty) (hsub : H ⊆ B.shifts)
    (Q R : Fin B.count → ZMod N → ℂ) {p : ℝ} (hqp : q ≤ p)
    (hsize : Real.exp (-p) * N ≤ (H.card : ℝ))
    (hQ : ∀ j n, ‖Q j n‖ ≤ 1) (hR : ∀ j n, ‖R j n‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ j, Real.exp (-p) ≤
      ‖𝔼 n, (B.mode h j).evalCyclic N (fun _ => n) * Q j n * R j (n + h)‖) :
    ∃ h₀ ∈ H, ∃ S ⊆ H, S.Nonempty ∧
      Real.exp (-(2 * p ^ 2 + p + 1)) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ j, Real.exp (-(2 * p ^ 2 + p + 1)) ≤
        ‖𝔼 n, partnerAnchorWeight
          (fun n => (B.mode h j).evalCyclic N (fun _ => n))
          (fun n => (B.mode h₀ j).evalCyclic N (fun _ => n)) (Q j) n *
            R j (n + h) * star (R j (n + h₀))‖ := by
  have hp : 0 ≤ p := (Nat.cast_nonneg B.dim).trans (B.geometry.1.trans hqp)
  have hK : (Fintype.card (Fin B.count) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans hqp)
  have hsize' : Real.exp (-p) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    simpa only [ZMod.card] using hsize
  obtain ⟨h₀, hh₀, S, hSH, hSn, hlarge, hanchor⟩ := exists_fixed_partner_anchor_power H hH
    (fun h j n => (B.mode h j).evalCyclic N (fun _ => n)) Q R hp hK hsize'
    (fun h hh j n => ((B.mode h j).norm_evalCyclic_le N _).trans (B.mode_norm h (hsub hh) j))
    hQ hR hcorr
  exact ⟨h₀, hh₀, S, hSH, hSn, by simpa only [ZMod.card] using hlarge, hanchor⟩

end Erdos3.PositiveShiftBasis

end

end OAI
