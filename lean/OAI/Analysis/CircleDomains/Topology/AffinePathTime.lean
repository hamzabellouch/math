import OAI.Analysis.CircleDomains.Topology.RationalTimeIntervals
import Mathlib.Topology.ContinuousMap.Interval

namespace OAI

/-! Increasing affine restriction maps and their clipped inverse on the
standard path interval. Interior inequalities remain exact after clipping. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def affinePathTime (a b : PathTime) : C(PathTime, PathTime) where
  toFun := fun t => Set.Icc.convexComb a b t
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun t : PathTime => (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ))
    fun_prop

theorem affinePathTime_coe (a b t : PathTime) :
    (affinePathTime a b t : ℝ) = ((b : ℝ) - a) * t + a := by
  change (1 - (t : ℝ)) * a + (t : ℝ) * b = _
  ring

theorem affinePathTime_zero (a b : PathTime) : affinePathTime a b ⊥ = a := by
  exact Set.Icc.convexComb_zero a b

theorem affinePathTime_one (a b : PathTime) : affinePathTime a b ⊤ = b := by
  exact Set.Icc.convexComb_one a b

theorem affinePathTime_strictMono {a b : PathTime} (hab : a < b) :
    StrictMono (affinePathTime a b) := by
  intro s t hst
  change (affinePathTime a b s : ℝ) < (affinePathTime a b t : ℝ)
  simp only [affinePathTime_coe]
  have h := mul_lt_mul_of_pos_left
    (show (s : ℝ) < t from hst) (sub_pos.mpr (show (a : ℝ) < b from hab))
  linarith

theorem affinePathTime_mem_Icc {a b : PathTime} (hab : a ≤ b) (t : PathTime) :
    affinePathTime a b t ∈ Icc a b := by
  have hmono : Monotone (affinePathTime a b) := by
    rcases hab.eq_or_lt with rfl | hlt
    · intro s t _
      simp [affinePathTime, Set.Icc.convexComb_eq]
    · exact (affinePathTime_strictMono hlt).monotone
  constructor
  · simpa only [affinePathTime_zero] using hmono (bot_le : (⊥ : PathTime) ≤ t)
  · simpa only [affinePathTime_one] using hmono (le_top : t ≤ (⊤ : PathTime))

def rescalePathTime (a b : PathTime) : C(PathTime, PathTime) where
  toFun := fun t => projIcc 0 1 zero_le_one (((t : ℝ) - a) / ((b : ℝ) - a))
  continuous_toFun := by fun_prop

theorem rescalePathTime_coe (a b t : PathTime) :
    (rescalePathTime a b t : ℝ) = max 0 (min 1 (((t : ℝ) - a) / ((b : ℝ) - a))) := rfl

theorem rescale_affinePathTime {a b : PathTime} (hab : a < b) (t : PathTime) :
    rescalePathTime a b (affinePathTime a b t) = t := by
  apply Subtype.ext
  rw [rescalePathTime_coe, affinePathTime_coe]
  have he : (((b : ℝ) - a) * t + a - a) / ((b : ℝ) - a) = t := by
    field_simp [ne_of_gt (sub_pos.mpr (show (a : ℝ) < b from hab))]
    ring
  rw [he, min_eq_right t.property.2, max_eq_right t.property.1]

theorem affine_rescalePathTime {a b : PathTime} (hab : a < b) {t : PathTime}
    (ht : t ∈ Icc a b) : affinePathTime a b (rescalePathTime a b t) = t := by
  have hden : 0 < (b : ℝ) - a := sub_pos.mpr hab
  have hzero : 0 ≤ ((t : ℝ) - a) / ((b : ℝ) - a) :=
    div_nonneg (sub_nonneg.mpr ht.1) hden.le
  have hone : ((t : ℝ) - a) / ((b : ℝ) - a) ≤ 1 := by
    apply (div_le_one hden).mpr
    exact sub_le_sub_right (show (t : ℝ) ≤ b from ht.2) _
  apply Subtype.ext
  rw [affinePathTime_coe, rescalePathTime_coe, min_eq_right hone, max_eq_right hzero]
  field_simp
  ring

theorem range_affinePathTime {a b : PathTime} (hab : a < b) :
    range (affinePathTime a b) = Icc a b := by
  apply Subset.antisymm
  · rintro t ⟨s, rfl⟩
    exact affinePathTime_mem_Icc hab.le s
  · intro t ht
    exact ⟨rescalePathTime a b t, affine_rescalePathTime hab ht⟩

theorem rescalePathTime_lt_iff {a b : PathTime} (hab : a < b) (s t : PathTime)
    (ht : ⊥ < t ∧ t < ⊤) :
    rescalePathTime a b s < t ↔ s < affinePathTime a b t := by
  change (rescalePathTime a b s : ℝ) < (t : ℝ) ↔ (s : ℝ) < affinePathTime a b t
  rw [rescalePathTime_coe, max_lt_iff, affinePathTime_coe]
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : (t : ℝ) < 1 := ht.2
  have hd : 0 < (b : ℝ) - a := sub_pos.mpr hab
  rw [and_iff_right ht0, min_lt_iff, or_iff_right (not_lt.mpr ht1.le), div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem lt_rescalePathTime_iff {a b : PathTime} (hab : a < b) (s t : PathTime)
    (ht : ⊥ < t ∧ t < ⊤) :
    t < rescalePathTime a b s ↔ affinePathTime a b t < s := by
  change (t : ℝ) < (rescalePathTime a b s : ℝ) ↔ (affinePathTime a b t : ℝ) < s
  rw [rescalePathTime_coe, lt_max_iff, affinePathTime_coe]
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : (t : ℝ) < 1 := ht.2
  have hd : 0 < (b : ℝ) - a := sub_pos.mpr hab
  rw [or_iff_right (not_lt.mpr ht0.le), lt_min_iff, and_iff_right ht1, lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

end CircleDomainRigidity

end

end OAI
