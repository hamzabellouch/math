import Mathlib
import OAI.Geometry.CAT0Fillings.Euler.NormalizedContradiction
import OAI.Geometry.CAT0Fillings.Scaling.Extremal

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open CurrentOperations

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
theorem extremal_coefficient_high {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    {c : ℝ} (hc : 0 < c) (hm : 0 < mass T)
    (hfill : ∀ (Y : Type u) [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
        [CompactSpace Y] [Nonempty Y], IsCAT0 Y →
      ∀ P : Functional Y (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      fillingVolume P ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      c*((mass T)^(fillingPower (k+2))-(mass B)^(fillingPower (k+2))) ≤ fillingVolume (T-B)) :
    c ≤ fillingCoefficient (k+2) := by
  by_contra hn
  obtain ⟨l,hl,hlm,hls,hln⟩ := normalized_scale (by omega : 0 < k+2) hm (lt_of_not_ge hn)
  let a : ℝ≥0 := ⟨l,hl.le⟩
  have : NeZero a := ⟨by exact NNReal.coe_ne_zero.mp hl.ne'⟩
  let Y := ScaledSpace X a
  have hY : IsCAT0 Y := ScaledSpace.isCAT0 a hX
  let U := pushCurrent (ScaledSpace.ofBase a) T
  have hU : IsIntegral (k+2) U := integral_push hT (ScaledSpace.up_lipschitz a)
  have hUz : boundarySucc U = 0 := pushCurrent_cycle hz (ScaledSpace.up_lipschitz a)
  have hUm : mass U = l^(k+2)*mass T := ScaledSpace.mass_up a hT.1
  have hUe := ScaledSpace.extremal_up a hX hT hz
    (by convert power_mul_dimension (by omega : 0 < k+2) using 1 <;> push_cast <;> ring) hext
  apply normalized_extremal_contradiction hk hY hU hUz (by rwa [hUm]) (by rwa [hUm]) hc
    (fillingPower_gt_one (by omega)) (by simpa only [Nat.cast_add,Nat.cast_ofNat,hUm] using hln) ?_ hUe
  intro P hP hPz
  obtain ⟨R,hR,hRb,hRm⟩ := hY.exists_minimal_integral_filling hP hPz
  exact ⟨R,hR,hRb,by rw [hRm]; exact hfill Y hY P hP hPz⟩
end CAT0Fillings
end

end OAI
