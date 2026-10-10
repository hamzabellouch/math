import OAI.MeasureTheory.Falconer.Incidence.OriginalCoarsePackets

namespace OAI

/-! Linear depth bounds for the dyadic losses used in packet preparation. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem bounded_planar_card_dyadic (N : ℕ) (P : Finset (Space 2))
    (hP : InBoundedLineChart P) (hsep : FiniteSeparatedAt (1/(2:ℝ)^N) P) :
    P.card ≤ 2^(2*N+5) := by
  have hball : ∀ p ∈ P, dist p 0 ≤ 2 := by
    intro p hp
    have hd := planar_dist_le_coordinate_sum p 0
    simp only [PiLp.zero_apply,sub_zero] at hd
    linarith only [hd,(hP p hp).1,(hP p hp).2]
  have hb := separated_ball_card P 0 (by positivity : 0 < 1/(2:ℝ)^N)
    (by norm_num : (0:ℝ) ≤ 2) hsep hball
  have hpow : (1:ℝ) ≤ 2^N := one_le_pow₀ (by norm_num)
  have hcalc : (2*(2:ℝ)/(1/2^N)+1)^2 ≤ (2:ℝ)^(2*N+5) := by
    calc
      _ = (4*(2:ℝ)^N+1)^2 := by field_simp; ring
      _ ≤ (5*(2:ℝ)^N)^2 := by gcongr; linarith only [hpow]
      _ ≤ 32*((2:ℝ)^N)^2 := by nlinarith only [sq_nonneg ((2:ℝ)^N)]
      _ = _ := by
        rw [show 2*N = N*2 by omega,pow_add,pow_mul]
        norm_num
        ring
  exact_mod_cast hb.trans hcalc

theorem packet_log_of_card_bound {m a : ℕ} (h : m ≤ 2^a) :
    Nat.log 2 m+1 ≤ a+1 :=
  Nat.add_le_add_right ((Nat.log_le_clog 2 m).trans (Nat.clog_le_of_le_pow h)) 1

theorem bounded_planar_log (N : ℕ) (P : Finset (Space 2))
    (hP : InBoundedLineChart P) (hsep : FiniteSeparatedAt (1/(2:ℝ)^N) P) :
    Nat.log 2 P.card+1 ≤ 2*N+6 := by
  simpa only [Nat.add_assoc] using packet_log_of_card_bound (bounded_planar_card_dyadic N P hP hsep)

theorem packet_incidence_log {a b : ℕ} (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (hP : P.card ≤ 2^a)
    (hT : (P.biUnion T).card ≤ 2^b) :
    Nat.log 2 (∑ p ∈ P, (T p).card)+1 ≤ a+b+1 := by
  apply packet_log_of_card_bound
  calc
    _ ≤ ∑ _p ∈ P, 2^b := Finset.sum_le_sum fun p hp =>
      (Finset.card_le_card (Finset.subset_biUnion_of_mem T hp)).trans hT
    _ = P.card*2^b := by simp
    _ ≤ 2^a*2^b := Nat.mul_le_mul_right _ hP
    _ = _ := (pow_add _ _ _).symm

end Falconer

end OAI
