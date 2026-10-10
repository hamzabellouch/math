import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeightLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedMultiplierLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityBounds

namespace OAI

/-! The actual transport-to-mass ratio is bounded uniformly on every fixed ball. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

variable (s : ℕ → ℕ) (hs : StrictMono s)
  (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
  (hz : Tendsto z atTop (𝓝 z₀))
  (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
    (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
  (hm : ∀ i, radialMatchingMap (s i) (z i)=0)

include s hs z hz hX hm

theorem radialMatched_uniform_transport_bound (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ i in atTop, ∀ r ∈ Icc 0 R,
      0 < radialMatchedMassFunction (s i) (z i) r ∧
      |radialMatchedTransportFunction (s i) (z i) r| ≤
        K*radialMatchedMassFunction (s i) (z i) r := by
  obtain ⟨c,M,hc,hM,_,hbound⟩ := radialMatched_uniform_weight_bounds s hs z z₀ hz hX hm R
  let K := 6*R*M/c
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with i hi
  intro r hr
  let mu := radialMatchedMassFunction (s i) (z i)
  have hmu := radialMatchedMassFunction_continuous (s i) (z i) (hX i) (hm i)
  have hmur : c ≤ mu r := (hi r hr).1
  have hmuM : ∀ t ∈ Icc 0 r, mu t ≤ M := by
    intro t ht
    exact (le_abs_self (mu t)).trans (by simpa only [mu,radialMatchedMassFunction,Real.norm_eq_abs] using (hi t ⟨ht.1,ht.2.trans hr.2⟩).2)
  have havg := radialAverage_mono mu (fun _ => M) hmu continuous_const r hr.1 hmuM
  rw [radialAverage_const] at havg
  have havg0 : 0 ≤ radialAverage mu r := radialAverage_nonneg mu r (by
    intro t ht
    exact sq_nonneg _)
  have ha := radialShootingA_bounds (s i) (profileMatchingParameter (z i))
  have hcs : 0 ≤ 6-2*radialShootingA (s i) := by linarith [ha.2]
  have hcs6 : 6-2*radialShootingA (s i) ≤ 6 := by linarith [ha.1]
  have hA0 : 0 ≤ radialMatchedTransportFunction (s i) (z i) r := by
    change 0 ≤ (6-2*radialShootingA (s i))*(r*radialAverage mu r)
    exact mul_nonneg hcs (mul_nonneg hr.1 havg0)
  refine ⟨hc.trans_le hmur,?_⟩
  rw [abs_of_nonneg hA0]
  change (6-2*radialShootingA (s i))*(r*radialAverage mu r) ≤ K*mu r
  calc
    _ ≤ 6*(R*M) := by
      apply mul_le_mul hcs6 _ (mul_nonneg hr.1 havg0) (by norm_num)
      exact mul_le_mul hr.2 (by linarith : radialAverage mu r ≤ M) havg0 hR
    _ = K*c := by dsimp only [K]; field_simp
    _ ≤ K*mu r := mul_le_mul_of_nonneg_left hmur hK

end DefocusingNLS

end OAI
