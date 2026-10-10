import OAI.Analysis.CircleDomains.Sobolev.SobolevCapacityScale
import OAI.Analysis.CircleDomains.Sobolev.SobolevEnergyMeasure
import OAI.Analysis.CircleDomains.Modulus.LengthContent

namespace OAI

/-! A quantitative Hausdorff-content bound obtained from actual local
Sobolev energy, whenever the coarse averages are small. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_lengthContent_le {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {A : Set (ℝ × ℝ)} (hA : ∀ c ∈ A, 1 ≤ u (euclideanPlaneCoordinates.symm c))
    (hmean : ∀ c ∈ A,
      |squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1| ≤ 1/2) :
    lengthContent A ≤ 131072 * coordinateSobolevEnergy V univ := by
  classical
  choose n hn using fun c : A => locally_sobolev_capacity_scale hu hw hLp c (hA c c.property)
    (hmean c c.property)
  let r : (ℝ × ℝ) → ℝ := fun c => if hc : c ∈ A then (1/4:ℝ)^(n ⟨c,hc⟩) else 1
  have hr : ∀ c ∈ A, 0 < r c := by
    intro c hc
    simp only [r, dite_eq_left hc]
    positivity
  have hb : ∀ c ∈ A, r c ≤ 1 := by
    intro c hc
    simp only [r, dite_eq_left hc]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hpay : ∀ c ∈ A, ENNReal.ofReal (r c) ≤
      16384 * coordinateSobolevEnergy V (closedBall c (r c)) := by
    intro c hc
    let E := ∫ p in coordinateSquare c (r c),
      (|V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|)^2
    have he : (1/128:ℝ)^2*r c ≤ E := by
      simpa only [r, dite_eq_left hc, E] using hn ⟨c,hc⟩
    have hh : r c ≤ 16384*E := by nlinarith
    have hm := coordinateSobolevEnergy_square V hLp c (r c)
    change coordinateSobolevEnergy V (closedBall c (r c)) = ENNReal.ofReal E at hm
    calc
      ENNReal.ofReal (r c) ≤ ENNReal.ofReal (16384*E) := ENNReal.ofReal_le_ofReal hh
      _ = 16384 * ENNReal.ofReal E := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ = _ := by rw [hm]
  have h := lengthContent_le_of_energy_payment hr hb (coordinateSobolevEnergy V) 16384 hpay
  norm_num at h ⊢
  exact h

end CircleDomainRigidity

end

end OAI
