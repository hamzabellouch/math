import OAI.Probability.BenjaminiSchramm.OpenTriangle

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

noncomputable def kernelTriangleDiagonal (G : BondGraph V E) (p : unitInterval)
    (K : V → V → ℝ≥0∞) (u : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, ∑' z, law p {ω | Conn G ω u a} * K a b *
    law p {ω | Conn G ω b z} * law p {ω | Conn G ω u z}

noncomputable def kernelDeletionDiagram (G : BondGraph V E) (p : unitInterval)
    (K : V → V → ℝ≥0∞) (x : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, ∑' z, K a b * law p {ω | Conn G ω b z} *
    law p {ω | Conn G ω x a ∧ Conn G ω x z}

theorem kernelDeletionDiagram_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (K : V → V → ℝ≥0∞)
    (ε : ℝ≥0∞) (hε : ∀ u, kernelTriangleDiagonal G p K u ≤ ε) (x : V) :
    kernelDeletionDiagram G p K x ≤ ε * ∑' u, law p {ω | Conn G ω x u} := by
  let f (a b z u : V) : ℝ≥0∞ := K a b * law p {ω | Conn G ω b z} *
    (law p {ω | Conn G ω x u} * law p {ω | Conn G ω u a} * law p {ω | Conn G ω u z})
  have hswap : (∑' a, ∑' b, ∑' z, ∑' u, f a b z u) =
      ∑' u, ∑' a, ∑' b, ∑' z, f a b z u := by
    calc
      _ = ∑' a, ∑' b, ∑' u, ∑' z, f a b z u :=
        tsum_congr (fun _ => tsum_congr (fun _ => ENNReal.tsum_comm))
      _ = ∑' a, ∑' u, ∑' b, ∑' z, f a b z u :=
        tsum_congr (fun _ => ENNReal.tsum_comm)
      _ = _ := ENNReal.tsum_comm
  calc
    _ ≤ ∑' a, ∑' b, ∑' z, K a b * law p {ω | Conn G ω b z} *
        (∑' u, law p {ω | Conn G ω x u} * law p {ω | Conn G ω u a} *
          law p {ω | Conn G ω u z}) :=
      ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
        ENNReal.tsum_le_tsum (fun z => mul_le_mul' le_rfl (three_arm_bound G p x a z))))
    _ = ∑' a, ∑' b, ∑' z, ∑' u, f a b z u := by
      simp only [f,ENNReal.tsum_mul_left]
    _ = ∑' u, ∑' a, ∑' b, ∑' z, f a b z u := hswap
    _ = ∑' u, law p {ω | Conn G ω x u} * kernelTriangleDiagonal G p K u := by
      apply tsum_congr
      intro u
      simp only [kernelTriangleDiagonal,←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro a
      apply tsum_congr
      intro b
      apply tsum_congr
      intro z
      dsimp only [f]
      ring
    _ ≤ ∑' u, law p {ω | Conn G ω x u} * ε :=
      ENNReal.tsum_le_tsum (fun u => mul_le_mul' le_rfl (hε u))
    _ = _ := by rw [ENNReal.tsum_mul_right,mul_comm]

end Percolation.BenjaminiSchramm

end OAI
