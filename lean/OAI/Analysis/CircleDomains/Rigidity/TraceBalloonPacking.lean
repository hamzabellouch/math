import OAI.Analysis.CircleDomains.Sobolev.SourceArea
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! Reserve each zero-radius balloon after removing all later balloons.
The reserved pieces are disjoint even when the balloons overlap. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def reservedBalloon (B : ℕ → Set ℂ) (j : ℕ) : Set ℂ :=
  B j \ ⋃ k : ℕ, B (k+j+1)

 theorem reservedBalloon_measurable {B : ℕ → Set ℂ}
    (hB : ∀ j, MeasurableSet (B j)) (j : ℕ) : MeasurableSet (reservedBalloon B j) :=
  (hB j).diff (MeasurableSet.iUnion (fun _ => hB _))

 theorem reservedBalloon_pairwise (B : ℕ → Set ℂ) :
    Pairwise (Disjoint on reservedBalloon B) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact hxi.2 (mem_iUnion.mpr ⟨j-i-1,by convert hxj.1 using 1; congr 1; omega⟩)
  · exact hxj.2 (mem_iUnion.mpr ⟨i-j-1,by convert hxi.1 using 1; congr 1; omega⟩)

 theorem reservedBalloon_area_lower {c : ℕ → ℂ} {d : ℕ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (hs : Summable (fun j => d j^2)) (j : ℕ)
    (htail : (∑' k : ℕ, d (k+j+1)^2) ≤ d j^2/2) :
    Real.pi*d j^2/2 ≤ volume.real (reservedBalloon (fun i => ball (c i) (d i)) j) := by
  let U := ⋃ k : ℕ, ball (c (k+j+1)) (d (k+j+1))
  have hsj : Summable (fun k : ℕ => d (k+j+1)^2) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (j+1)).mpr hs
  have hreal : Summable (fun k : ℕ => volume.real (ball (c (k+j+1)) (d (k+j+1)))) :=
    (hsj.mul_left Real.pi).congr (fun k => (real_volume_ball _ (hd _)).symm)
  have hsum : (∑' k : ℕ, volume (ball (c (k+j+1)) (d (k+j+1)))) ≠ ∞ := by
    have hh := hreal.tsum_ofReal_ne_top
    simpa only [measureReal_def,ENNReal.ofReal_toReal measure_ball_lt_top.ne] using hh
  have hUf : volume U ≠ ∞ := ne_of_lt ((measure_iUnion_le _).trans_lt (lt_top_iff_ne_top.mpr hsum))
  have hU : volume.real U ≤ Real.pi*(∑' k : ℕ, d (k+j+1)^2) := by
    have hh := ENNReal.toReal_mono hsum (measure_iUnion_le
      (fun k : ℕ => ball (c (k+j+1)) (d (k+j+1))))
    rw [ENNReal.tsum_toReal_eq (fun _ => measure_ball_lt_top.ne)] at hh
    simpa only [← measureReal_def,real_volume_ball _ (hd _),hsj.tsum_mul_left] using hh
  have hdiff := le_measureReal_sdiff (μ := (volume : Measure ℂ))
    (s₁ := ball (c j) (d j)) (s₂ := U) hUf
  rw [show volume.real (ball (c j) (d j)) = Real.pi*d j^2 from real_volume_ball _ (hd j)] at hdiff
  change Real.pi*d j^2/2 ≤ volume.real (ball (c j) (d j) \ U)
  nlinarith [mul_le_mul_of_nonneg_left htail Real.pi_pos.le]

end CircleDomainRigidity

end

end OAI
