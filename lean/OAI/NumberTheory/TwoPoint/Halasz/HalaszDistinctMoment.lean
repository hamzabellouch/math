import OAI.NumberTheory.TwoPoint.Halasz.HalaszCollisionPartition

namespace OAI

/-! At least half the complete-system solutions have distinct chosen
long coordinates on both sides, once the elementary size threshold holds. -/
namespace TwoPointCorrelations

theorem halasz_distinct_moment {s k n N ℓ : ℕ} (hs : 0<s) (hk : 2≤k)
    (hn : n+2=s+k) (L : Fin ℓ → Fin (n+2)) (hL : Function.Injective L)
    (hN : (4*(ℓ:ℝ)^2)^2<(N:ℝ)) :
    halaszVinogradovCount (n+2) k N ≤
      2*halaszFiberEnergy (halaszGoodLongTuples (N := N) L) (halaszVinogradovFrequency k) := by
  have hp := halasz_long_collision_partition (k := k) (N := N) L hL
  have hpR : (halaszVinogradovCount (n+2) k N:ℝ) ≤
      2*((ℓ:ℝ)^2*(halaszRepeatedCount n k N:ℝ)) +
        (halaszFiberEnergy (halaszGoodLongTuples (N := N) L)
          (halaszVinogradovFrequency k):ℝ) := by exact_mod_cast hp
  have hn' : n=s+k-2 := by omega
  have hr : (halaszRepeatedCount n k N:ℝ) ≤ halaszCollisionMoment s k N := by
    rw [hn']
    exact halasz_repeated_count_bound hk N
  have hc : 0≤4*(ℓ:ℝ)^2 := by positivity
  have hsmall := halasz_collision_moment_small hs hk hc hN
  rw [← hn] at hsmall
  have hbad := mul_le_mul_of_nonneg_left hr hc
  have he : (halaszVinogradovCount (n+2) k N:ℝ) <
      2*(halaszFiberEnergy (halaszGoodLongTuples (N := N) L)
        (halaszVinogradovFrequency k):ℝ) := by
    nlinarith only [hpR,hsmall,hbad]
  exact_mod_cast he.le

end TwoPointCorrelations

end OAI
