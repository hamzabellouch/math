import OAI.Analysis.CircleDomains.Sobolev.SobolevLengthCapacity

namespace OAI

/-! The capacity estimate retains its countable positive-radius ball cover,
so its cost can be transported to a small-diameter cover of the graph. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_unit_ball_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (huL2 : MemLp (fun p => u (euclideanPlaneCoordinates.symm p)) 2 volume)
    {A : Set (ℝ × ℝ)} (hA : A ⊆ closedBall 0 1)
    (hone : ∀ c ∈ A, 1 ≤ u (euclideanPlaneCoordinates.symm c)) :
    ∃ (U : Set (ℝ × ℝ)) (r : (ℝ × ℝ) → ℝ), U.Countable ∧
      (∀ x ∈ U, 0 < r x ∧ r x ≤ 4) ∧
      A ⊆ ⋃ x : U, closedBall (x : ℝ × ℝ) (r x) ∧
      (∑' x : U, ENNReal.ofReal (r x)) ≤ 131072 *
        (ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
          coordinateSobolevEnergy V univ) := by
  classical
  by_cases hs : (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) ≤ 1
  · have hmean (c : ℝ × ℝ) :
        |squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c 1| ≤ 1/2 :=
      abs_unitSquareAverage_le_half huL2 hs c
    choose n hn using fun c : A => locally_sobolev_capacity_scale hu hw hLp c (hone c c.property) (hmean c)
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
        _ = 16384*ENNReal.ofReal E := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
        _ = _ := by rw [hm]
    obtain ⟨U,hUA,hUc,hcover,hcost⟩ := energy_ball_cover hr hb (coordinateSobolevEnergy V) 16384 hpay
    refine ⟨U,fun x => 4*r x,hUc,(fun x hx => ⟨mul_pos (by norm_num) (hr x (hUA hx)), by linarith [hb x (hUA hx)]⟩),hcover,?_⟩
    have hsum : (∑' x : U, ENNReal.ofReal (4*r x)) = 4*∑' x : U, ENNReal.ofReal (r x) := by
      simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4), ENNReal.ofReal_ofNat]
      exact ENNReal.tsum_mul_left
    rw [hsum]
    calc
      _ ≤ 4*(16384*coordinateSobolevEnergy V univ) := mul_le_mul' le_rfl hcost
      _ ≤ 131072*(ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
          coordinateSobolevEnergy V univ) := by
        rw [← mul_assoc]
        apply mul_le_mul'
        · norm_num
        · exact le_add_of_nonneg_left (by positivity)
  · refine ⟨{0},fun _ => 1,countable_singleton _,(by simp),?_,?_⟩
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨0,mem_singleton 0⟩,hA hx⟩
    · have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) := by
        exact_mod_cast (ENNReal.ofReal_le_ofReal (le_of_not_ge hs))
      have hcard : (∑' _x : ({0} : Set (ℝ × ℝ)), (1 : ℝ≥0∞)) = 1 := by simp
      simp only [ENNReal.ofReal_one]
      change (∑' _x : ({0} : Set (ℝ × ℝ)), (1 : ℝ≥0∞)) ≤ _
      rw [hcard]
      calc
        1 ≤ 131072*(1:ℝ≥0∞) := by norm_num
        _ ≤ _ := mul_le_mul' le_rfl (h1.trans (le_add_of_nonneg_right (by positivity)))

end CircleDomainRigidity

end

end OAI
