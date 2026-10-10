import OAI.Probability.BenjaminiSchramm.ExteriorConnection

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def kernelExteriorPotential (G : BondGraph V E) (p : unitInterval)
    (K : V → V → ℝ≥0∞) (x : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, K a b * exteriorConnectionMoment G p x a b

theorem kernelExteriorPotential_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (K : V → V → ℝ≥0∞)
    (hK : ∀ a, ∑' b, K a b = 1) (c C : ℝ≥0∞)
    (hc : ∀ b, c ≤ ENNReal.ofReal (susceptibility G p b))
    (hC : ∀ b, ENNReal.ofReal (susceptibility G p b) ≤ C) (x : V) :
    c * (∑' a, law p {ω | Conn G ω x a}) ≤
      kernelExteriorPotential G p K x + C * kernelDeletionDiagram G p K x := by
  calc
    _ = ∑' a, ∑' b, K a b *
        (law p {ω | Conn G ω x a} * c) := by
      simp only [ENNReal.tsum_mul_right,hK,one_mul,mul_comm c]
    _ ≤ ∑' a, ∑' b, K a b *
        (law p {ω | Conn G ω x a} * ENNReal.ofReal (susceptibility G p b)) :=
      ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hc b))))
    _ ≤ ∑' a, ∑' b, K a b *
        (exteriorConnectionMoment G p x a b + C *
          ∑' z, law p {ω | Conn G ω x a ∧ Conn G ω x z} * law p {ω | Conn G ω b z}) :=
      ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
        mul_le_mul' le_rfl (connection_exterior_comparison G hloc hqt p hp C hC x a b)))
    _ = _ := by
      simp only [mul_add,ENNReal.tsum_add,kernelExteriorPotential,kernelDeletionDiagram]
      congr 1
      simp only [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro a
      apply tsum_congr
      intro b
      apply tsum_congr
      intro z
      ring

theorem kernelExteriorPotential_lower_of_critical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (T K : Hilbert V →L[ℂ] Hilbert V)
    (hT : HasKernel G (pc G) T) (hK : PositiveRealMatrix K)
    (hrow : ∀ a, ∑' b, ennMatrixCoeff K a b = 1) (c C : ℝ≥0∞)
    (hc : ∀ b, c ≤ ENNReal.ofReal (susceptibility G p b))
    (hC : ∀ b, ENNReal.ofReal (susceptibility G p b) ≤ C) (x : V) :
    c * ENNReal.ofReal (susceptibility G p x) ≤
      kernelExteriorPotential G p (ennMatrixCoeff K) x +
        C * ENNReal.ofReal (‖T‖^3 * ‖K‖) * ENNReal.ofReal (susceptibility G p x) := by
  have hh := kernelExteriorPotential_lower G hloc hqt p hp (ennMatrixCoeff K) hrow c C hc hC x
  rw [←ennreal_susceptibility G hloc hqt p hp x] at hh
  apply hh.trans
  apply add_le_add_right
  have he := kernelDeletionDiagram_le_critical_norm G T K hT hK p hp.le x
  rw [←ennreal_susceptibility G hloc hqt p hp x] at he
  simpa only [mul_assoc] using mul_le_mul' (le_refl C) he

end Percolation.BenjaminiSchramm

end OAI
