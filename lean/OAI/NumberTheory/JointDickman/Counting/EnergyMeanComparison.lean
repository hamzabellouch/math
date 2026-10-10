import OAI.NumberTheory.JointDickman.Counting.CountingPeriodicEnergy
import OAI.NumberTheory.JointDickman.Counting.BlockCutNorm

namespace OAI

/-! # Passing from periodic mean-square energy to mean energy -/
namespace JointDickman
open Finset Classical

theorem complexEnergy_sub {ι : Type*} [Fintype ι]
    (K J : ι → ι → ℝ) (z : ι → ℂ) :
    complexEnergy (fun i k => K i k-J i k) z = complexEnergy K z-complexEnergy J z := by
  simp only [complexEnergy,Complex.ofReal_sub,sub_mul,sum_sub_distrib]

theorem normalized_energy_comparison {M : ℕ} (hM : 0 < M)
    (K J : Fin M → Fin M → ℝ) (z : Fin M → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    |(complexEnergy K z).re|/(M : ℝ) ≤ |(complexEnergy J z).re|/(M : ℝ)+
      16*kernelCutNorm (fun i k => K i k-J i k) := by
  have h := complexEnergy_re_cutNorm_le M (fun i k => K i k-J i k) z hz
  rw [complexEnergy_sub,Complex.sub_re] at h
  have ht : |(complexEnergy K z).re| ≤
      |(complexEnergy K z).re-(complexEnergy J z).re|+|(complexEnergy J z).re| := by
    simpa only [sub_add_cancel] using abs_add_le
      ((complexEnergy K z).re-(complexEnergy J z).re) (complexEnergy J z).re
  apply (div_le_div_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ M)).trans
  rw [add_div]
  linarith

theorem finite_norm_mean_of_square {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    {X t δ : ℝ} (hX : 0 < X) (ht : 0 < t) (hcard : (S.card : ℝ) ≤ 2*X)
    (hsquare : (1/X)*(∑ i ∈ S, ‖f i‖^2) ≤ δ) :
    (1/X)*(∑ i ∈ S, ‖f i‖) ≤ 2*t+δ/(4*t) := by
  have hp (i : ι) : ‖f i‖ ≤ t+‖f i‖^2/(4*t) := by
    have hh : ‖f i‖*(4*t) ≤ t*(4*t)+‖f i‖^2 := by
      nlinarith [sq_nonneg (‖f i‖-2*t)]
    have hd := (le_div_iff₀ (by positivity : 0 < 4*t)).mpr hh
    exact hd.trans_eq (by field_simp)
  calc
    _ ≤ (1/X)*(∑ i ∈ S, (t+‖f i‖^2/(4*t))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hp i)) (by positivity)
    _ = ((S.card : ℝ)/X)*t+((1/X)*(∑ i ∈ S, ‖f i‖^2))/(4*t) := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul,← sum_div]
      ring
    _ ≤ 2*t+δ/(4*t) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ ht.le
        exact (div_le_iff₀ hX).mpr hcard
      · exact div_le_div_of_nonneg_right hsquare (by positivity)

end JointDickman

end OAI
