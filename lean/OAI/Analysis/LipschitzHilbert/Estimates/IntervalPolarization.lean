import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketDifferentiation
import OAI.Analysis.LipschitzHilbert.Packets.PacketPolarization

namespace OAI

/-! Four-phase polarization commutes with the finite scale interval.
The analyzing coefficients and synthesizing waves remain separate. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def polarizedPacketInterval
    (a b : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f h : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (c : ℂ) (lower upper : ℕ) (x y : ℝ) : EuclideanSpace ℂ κ :=
  planarPacketInterval (fun j u => a j u + conj c • b j u)
    (fun j u k t s => f j u k t s + c * h j u k t s) lower upper x y

omit [Fintype κ] in
theorem planarPacketInterval_cross_polarization
    (a b : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f h : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (lower upper : ℕ) (x y : ℝ) :
    (4 : ℂ) • planarPacketInterval a h lower upper x y =
      polarizedPacketInterval a b f h 1 lower upper x y -
      polarizedPacketInterval a b f h (-1) lower upper x y -
      Complex.I • polarizedPacketInterval a b f h Complex.I lower upper x y +
      Complex.I • polarizedPacketInterval a b f h (-Complex.I) lower upper x y := by
  ext k
  have hband (j : Fin N) :
      (4 : ℂ) * planarPacketBand a h j k x y =
        planarPacketBand (fun j u => a j u + b j u)
          (fun j u k t s => f j u k t s + h j u k t s) j k x y -
        planarPacketBand (fun j u => a j u - b j u)
          (fun j u k t s => f j u k t s - h j u k t s) j k x y -
        Complex.I * planarPacketBand (fun j u => a j u - Complex.I • b j u)
          (fun j u k t s => f j u k t s + Complex.I * h j u k t s) j k x y +
        Complex.I * planarPacketBand (fun j u => a j u + Complex.I • b j u)
          (fun j u k t s => f j u k t s - Complex.I * h j u k t s) j k x y := by
    simp only [planarPacketBand, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact (packet_cross_polarization (a j u k) (b j u k)
      (f j u k y x) (h j u k y x)).symm
  have hpartial (n : ℕ) :
      (4 : ℂ) * scalarBandPartial (fun j => planarPacketBand a h j k x) n y =
        scalarBandPartial (fun j => planarPacketBand (fun j u => a j u + b j u)
          (fun j u k t s => f j u k t s + h j u k t s) j k x) n y -
        scalarBandPartial (fun j => planarPacketBand (fun j u => a j u - b j u)
          (fun j u k t s => f j u k t s - h j u k t s) j k x) n y -
        Complex.I * scalarBandPartial (fun j => planarPacketBand
          (fun j u => a j u - Complex.I • b j u)
          (fun j u k t s => f j u k t s + Complex.I * h j u k t s) j k x) n y +
        Complex.I * scalarBandPartial (fun j => planarPacketBand
          (fun j u => a j u + Complex.I • b j u)
          (fun j u k t s => f j u k t s - Complex.I * h j u k t s) j k x) n y := by
    simp only [scalarBandPartial, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < n
    · simp only [hj, ite_true]
      exact hband j
    · simp only [hj, ite_false, mul_zero, sub_zero, add_zero]
  simp only [polarizedPacketInterval, planarPacketInterval, bandIntervalSignal,
    WithLp.ofLp_smul, WithLp.ofLp_add, WithLp.ofLp_sub,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    map_one, map_neg, Complex.conj_I, one_smul, neg_smul, neg_mul,
    one_mul, neg_neg, ← sub_eq_add_neg]
  linear_combination hpartial upper - hpartial lower

theorem four_phase_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x A B C D : E) (h : (4 : ℂ) • x = A - B - Complex.I • C + Complex.I • D) :
    4 * ‖x‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  have hn := calc
    ‖A - B - Complex.I • C + Complex.I • D‖ ≤
        ‖A - B - Complex.I • C‖ + ‖Complex.I • D‖ := norm_add_le _ _
    _ ≤ (‖A - B‖ + ‖Complex.I • C‖) + ‖Complex.I • D‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (‖A‖ + ‖B‖ + ‖Complex.I • C‖) + ‖Complex.I • D‖ :=
      add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
  rw [← h] at hn
  simpa only [norm_smul, Complex.norm_I, one_mul, Complex.norm_ofNat] using hn

theorem four_phase_joint_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x dx : E) (F DF : Fin 4 → E) (W B : ℝ) (hW : 0 ≤ W)
    (hx : (4 : ℂ) • x = F 0 - F 1 - Complex.I • F 2 + Complex.I • F 3)
    (hdx : (4 : ℂ) • dx = DF 0 - DF 1 - Complex.I • DF 2 + Complex.I • DF 3)
    (hbound : ∀ i, ‖F i‖ + W * ‖DF i‖ ≤ B) :
    ‖x‖ + W * ‖dx‖ ≤ B := by
  have hn := four_phase_norm_le x (F 0) (F 1) (F 2) (F 3) hx
  have hd := mul_le_mul_of_nonneg_left
    (four_phase_norm_le dx (DF 0) (DF 1) (DF 2) (DF 3) hdx) hW
  linarith [hbound 0, hbound 1, hbound 2, hbound 3]

end LipschitzHilbert

end

end OAI
