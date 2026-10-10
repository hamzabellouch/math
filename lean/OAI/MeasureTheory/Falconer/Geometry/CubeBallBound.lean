import OAI.MeasureTheory.Falconer.Geometry.CubeBallPacking
import OAI.MeasureTheory.Falconer.Measures.CubeProbability
import OAI.MeasureTheory.Falconer.Frostman.Frostman

namespace OAI

/-! # Uniform Frostman ball bounds for the finite cube approximants -/
namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

theorem cube_ball_measure_le {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (hcarry : μ Q.carrierᶜ = 0)
    (s C : ℝ) (_hC : 0 ≤ C) (n : ℕ)
    (hb : ∀ p : List (Fin d → Bool), p.length = n →
      μ (Q.descendant p).carrier ≤ ENNReal.ofReal (C*(Q.descendant p).side^s))
    (x : Space d) {r : ℝ} (hr : r ≤ Q.side/(2:ℝ)^n) :
    μ (ball x r) ≤ ENNReal.ofReal ((7:ℝ)^d*C*(Q.side/(2:ℝ)^n)^s) := by
  classical
  let S := cubeBallHits Q n x r
  have hcover : ball x r ⊆ (⋃ p ∈ S, (Q.descendant p).carrier) ∪ Q.carrierᶜ := by
    intro z hz
    by_cases hQz : z ∈ Q.carrier
    · obtain ⟨p,hp,hzp⟩ := Q.mem_descendant_at_depth n hQz
      exact Or.inl (mem_iUnion₂.mpr ⟨p,(mem_cubeBallHits Q n x r p).mpr
        ⟨(mem_cubePaths d n p).mp hp,⟨z,hzp,hz⟩⟩,hzp⟩)
    · exact Or.inr hQz
  calc
    μ (ball x r) ≤ μ ((⋃ p ∈ S, (Q.descendant p).carrier) ∪ Q.carrierᶜ) := measure_mono hcover
    _ ≤ μ (⋃ p ∈ S, (Q.descendant p).carrier)+μ Q.carrierᶜ := measure_union_le _ _
    _ = μ (⋃ p ∈ S, (Q.descendant p).carrier) := by rw [hcarry,add_zero]
    _ ≤ ∑ p ∈ S, μ (Q.descendant p).carrier := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ S, ENNReal.ofReal (C*(Q.side/(2:ℝ)^n)^s) := by
      apply Finset.sum_le_sum
      intro p hp
      have hl := ((mem_cubeBallHits Q n x r p).mp hp).1
      simpa only [Q.descendant_side,hl] using hb p hl
    _ ≤ (7^d:ℕ)*ENNReal.ofReal (C*(Q.side/(2:ℝ)^n)^s) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_left (by exact_mod_cast cubeBallHits_card Q hQ n x hr) _
    _ = _ := by
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring

theorem eventual_cube_ball_bounds {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (μ : ℕ → ProbabilityMeasure (Space d))
    (hcarry : ∀ K, (μ K : Measure (Space d)) Q.carrierᶜ = 0)
    (hb : ∀ K, ∀ p : List (Fin d → Bool), p.length ≤ K →
      (μ K : Measure (Space d)) (Q.descendant p).carrier ≤
        ENNReal.ofReal (c⁻¹*(Q.descendant p).side^s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space d, ∀ r > 0, ∀ᶠ K in atTop,
      (μ K : Measure (Space d)) (ball x r) ≤ ENNReal.ofReal (C*r^s) := by
  let C := max ((7:ℝ)^d*c⁻¹*(2:ℝ)^s) (Q.side^s)⁻¹
  have hside : 0 < Q.side^s := Real.rpow_pos_of_pos hQ s
  have hC : 0 < C := (inv_pos.mpr hside).trans_le (le_max_right _ _)
  refine ⟨C,hC,fun x r hr => ?_⟩
  by_cases hrQ : r ≤ Q.side
  · obtain ⟨n,hrn,hnr⟩ := PlanarFalconer.exists_dyadic_scale hQ hr hrQ
    filter_upwards [eventually_ge_atTop n] with K hK
    have hball := cube_ball_measure_le Q hQ (μ K) (hcarry K) s c⁻¹
      (by positivity) n (fun p hp => hb K p (hp ▸ hK)) x hrn
    apply hball.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ Q.side/(2:ℝ)^n) hnr.le hs.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le] at hp
    calc
      (7:ℝ)^d*c⁻¹*(Q.side/(2:ℝ)^n)^s ≤ (7:ℝ)^d*c⁻¹*((2:ℝ)^s*r^s) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = ((7:ℝ)^d*c⁻¹*(2:ℝ)^s)*r^s := by ring
      _ ≤ C*r^s := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · apply Filter.Eventually.of_forall
    intro K
    have hpow := Real.rpow_le_rpow hQ.le (le_of_not_ge hrQ) hs.le
    have hlarge : 1 ≤ C*r^s := by
      calc
        1 = (Q.side^s)⁻¹*Q.side^s := (inv_mul_cancel₀ hside.ne').symm
        _ ≤ (Q.side^s)⁻¹*r^s := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ C*r^s := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    calc
      (μ K : Measure (Space d)) (ball x r) ≤ (μ K : Measure (Space d)) univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (C*r^s) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hlarge

end Falconer

end OAI
