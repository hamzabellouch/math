import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.GeneralPush
import OAI.Geometry.CAT0Fillings.Fillings.Attainment
import OAI.Geometry.CAT0Fillings.Scaling.Metric

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.ScaledSpace
open CurrentOperations

lemma push_down_up {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (c : ℝ≥0) [NeZero c]
    {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T) :
    pushCurrent (toBase c) (pushCurrent (ofBase c) T) = T := by
  rw [←pushCurrent_comp (down_lipschitz c)]
  exact pushCurrent_id hT
lemma push_up_down {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (c : ℝ≥0) [NeZero c]
    {n : ℕ} {T : Functional (ScaledSpace X c) n} (hT : IsMetricCurrent T) :
    pushCurrent (ofBase c) (pushCurrent (toBase c) T) = T := by
  rw [←pushCurrent_comp (up_lipschitz c)]
  exact pushCurrent_id hT
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] (c : ℝ≥0) [NeZero c]
lemma mass_up {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T) :
    mass (pushCurrent (ofBase c) T) = (c:ℝ)^n*mass T := by
  have hc : 0 < (c:ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero (NeZero.ne c))
  apply le_antisymm (mass_pushCurrent_le hT (up_lipschitz c))
  have hl := mass_pushCurrent_le (pushCurrent_isMetricCurrent hT (up_lipschitz c)) (down_lipschitz c)
  rw [push_down_up c hT,NNReal.coe_inv,inv_pow] at hl
  have hh := mul_le_mul_of_nonneg_left hl (pow_nonneg hc.le n)
  simpa only [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero n hc.ne'),one_mul] using hh
lemma mass_down {n : ℕ} {T : Functional (ScaledSpace X c) n} (hT : IsMetricCurrent T) :
    mass (pushCurrent (toBase c) T) = ((c:ℝ)^n)⁻¹*mass T := by
  have h := mass_up c (pushCurrent_isMetricCurrent hT (down_lipschitz c))
  rw [push_up_down c hT] at h
  rw [h,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero n (NNReal.coe_ne_zero.mpr (NeZero.ne c))),one_mul]
lemma filling_up (hX : IsCAT0 X) {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    fillingVolume (pushCurrent (ofBase c) T) = (c:ℝ)^(k+2)*fillingVolume T := by
  have hTi := integral_push hT (up_lipschitz c)
  have hTz := pushCurrent_cycle hz (up_lipschitz c)
  obtain ⟨S,hS,hSb,hSm⟩ := hX.exists_minimal_integral_filling hT hz
  obtain ⟨R,hR,hRb,hRm⟩ := (isCAT0 c hX).exists_minimal_integral_filling hTi hTz
  apply le_antisymm
  · have hh := fillingVolume_le (integral_push hS (up_lipschitz c))
      (by rw [pushCurrent_boundarySucc S (up_lipschitz c),hSb])
    simpa only [mass_up c hS.1,hSm] using hh
  · have hh := fillingVolume_le (integral_push hR (down_lipschitz c))
      (show boundarySucc (pushCurrent (toBase c) R) = T by
        rw [pushCurrent_boundarySucc R (down_lipschitz c),hRb,push_down_up c hT.1])
    rw [mass_down c hR.1,hRm] at hh
    have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg c.coe_nonneg (k+2))
    simpa only [←mul_assoc,mul_inv_cancel₀
      (pow_ne_zero (k+2) (NNReal.coe_ne_zero.mpr (NeZero.ne c))),one_mul] using hm
end CAT0Fillings.ScaledSpace
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.ScaledSpace
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] (c : ℝ≥0) [NeZero c]
lemma mass_up_rpow {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T) (p : ℝ) :
    (mass (pushCurrent (ofBase c) T))^p = (c:ℝ)^((n:ℝ)*p)*(mass T)^p := by
  rw [mass_up c hT,Real.mul_rpow (pow_nonneg c.coe_nonneg n) (mass_nonneg T),
    ←Real.rpow_natCast (c:ℝ) n,←Real.rpow_mul c.coe_nonneg]
lemma extremal_up (hX : IsCAT0 X) {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) {d p : ℝ}
    (hp : (k+1:ℝ)*p = (k+2:ℝ))
    (hext : ∀ B : Functional X (k+1), IsIntegral (k+1) B → boundarySucc B = 0 →
      d*((mass T)^p-(mass B)^p) ≤ fillingVolume (T-B)) :
    ∀ B : Functional (ScaledSpace X c) (k+1), IsIntegral (k+1) B → boundarySucc B = 0 →
      d*((mass (pushCurrent (ofBase c) T))^p-(mass B)^p) ≤
        fillingVolume (pushCurrent (ofBase c) T-B) := by
  intro B hB hBz
  let D := pushCurrent (toBase c) B
  have hD : IsIntegral (k+1) D := integral_push hB (down_lipschitz c)
  have hDz : boundarySucc D = 0 := pushCurrent_cycle hBz (down_lipschitz c)
  have hDB : pushCurrent (ofBase c) D = B := push_up_down c hB.1
  have hsub : pushCurrent (ofBase c) (T-D) = pushCurrent (ofBase c) T-B := by
    rw [←hDB]
    funext b π
    simp only [pushCurrent,Pi.sub_apply]
    split <;> simp
  have hp' : ((k+1:ℕ):ℝ)*p = ((k+2:ℕ):ℝ) := by simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hp
  have h := mul_le_mul_of_nonneg_left (hext D hD hDz) (pow_nonneg c.coe_nonneg (k+2))
  rw [←filling_up c hX (hT.sub hD) (by rw [boundarySucc_sub,hz,hDz,sub_self]),hsub] at h
  have hmp := mass_up_rpow c hT.1 p
  have hmd := mass_up_rpow c hD.1 p
  rw [hp',Real.rpow_natCast] at hmp hmd
  rw [hDB] at hmd
  rw [hmp,hmd]
  convert h using 1; first | rfl | ring
end CAT0Fillings.ScaledSpace
end

end OAI
