import Mathlib
import OAI.Combinatorics.HoneycombCorridor.LateralMass
import OAI.Combinatorics.HoneycombCorridor.StripWindows

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def shellRatio : ℝ := Real.exp (-tailRate)
noncomputable def spatialConstant : ℝ :=
  20 * (1 + ∑' n : ℕ, ((n : ℝ)+1)*shellRatio^n)

 theorem shellRatio_range : 0 < shellRatio ∧ shellRatio < 1 := by
  constructor
  · exact Real.exp_pos _
  · exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos tailRate_pos)

theorem shellSeries_summable : Summable (fun n : ℕ => ((n : ℝ)+1)*shellRatio^n) := by
  have hn : ‖shellRatio‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_pos shellRatio_range.1]
    exact shellRatio_range.2
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h0 := summable_geometric_of_norm_lt_one hn
  simpa only [pow_one,add_mul,one_mul] using h1.add h0

theorem spatialConstant_pos : 0 < spatialConstant := by
  have h : 0 ≤ ∑' n : ℕ, ((n : ℝ)+1)*shellRatio^n :=
    tsum_nonneg (fun n => mul_nonneg (by positivity) (pow_nonneg shellRatio_range.1.le _))
  dsimp [spatialConstant]
  linarith

noncomputable def shellIndex (h : ℕ) (v : Vertex) : ℕ :=
  ⌊|(position v).1|/(2*((h : ℝ)+1))⌋₊

theorem shellIndex_bounds (h : ℕ) (v : Vertex) :
    (shellIndex h v : ℝ) ≤ |(position v).1|/(2*((h : ℝ)+1)) ∧
    |(position v).1| < 2*((shellIndex h v : ℝ)+1)*((h : ℝ)+1) := by
  have hd : (0 : ℝ) < 2*((h : ℝ)+1) := by positivity
  refine ⟨Nat.floor_le (div_nonneg (abs_nonneg _) hd.le),?_⟩
  have hh := Nat.lt_floor_add_one (|(position v).1|/(2*((h : ℝ)+1)))
  have hi := (div_lt_iff₀ hd).mp hh
  dsimp [shellIndex]
  nlinarith

theorem spatial_sum_exp_bound (h : ℕ) (D : Finset Vertex)
    (hstrip : ∀ v ∈ D, InStrip h v) :
    (∑ v ∈ D, Real.exp (-tailRate*|(position v).1|/(2*(h+1)))) ≤
      spatialConstant*((h : ℝ)+1)^2 := by
  classical
  let S := D.image (shellIndex h)
  have hsplit := Finset.sum_fiberwise_of_maps_to
    (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩ : ∀ v ∈ D, shellIndex h v ∈ S)
    (fun v => Real.exp (-tailRate*|(position v).1|/(2*(h+1))))
  rw [← hsplit]
  have hs : ∀ n ∈ S,
      (∑ v ∈ D with shellIndex h v = n,
        Real.exp (-tailRate*|(position v).1|/(2*(h+1)))) ≤
      20*((n : ℝ)+1)*((h : ℝ)+1)^2 * shellRatio^n := by
    intro n hn
    have hc := strip_shell_card_le h n D hstrip (D.filter (fun v => shellIndex h v = n))
      (Finset.filter_subset _ _) (by
        intro v hv
        obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
        simpa only [he] using (shellIndex_bounds h v).2)
    calc
      _ ≤ ∑ v ∈ D with shellIndex h v = n, shellRatio^n := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
        rw [shellRatio,← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hl := (shellIndex_bounds h v).1
        rw [he] at hl
        have hm := mul_le_mul_of_nonpos_left hl (neg_nonpos.mpr tailRate_pos.le)
        calc
          -tailRate*|(position v).1|/(2*(h+1)) =
              -tailRate*(|(position v).1|/(2*(h+1))) := by ring
          _ ≤ -tailRate*(n : ℝ) := hm
          _ = (n : ℝ)*-tailRate := by ring
      _ = ((D.filter (fun v => shellIndex h v = n)).card : ℝ) * shellRatio^n := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (pow_nonneg shellRatio_range.1.le _)
  calc
    _ ≤ ∑ n ∈ S, 20*((n : ℝ)+1)*((h : ℝ)+1)^2 * shellRatio^n :=
      Finset.sum_le_sum hs
    _ = 20*((h : ℝ)+1)^2 * ∑ n ∈ S, ((n : ℝ)+1)*shellRatio^n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ 20*((h : ℝ)+1)^2 * (∑' n : ℕ, ((n : ℝ)+1)*shellRatio^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact shellSeries_summable.sum_le_tsum S
        (fun n _ => mul_nonneg (by positivity) (pow_nonneg shellRatio_range.1.le _))
    _ ≤ spatialConstant*((h : ℝ)+1)^2 := by
      dsimp [spatialConstant]
      nlinarith [sq_nonneg ((h : ℝ)+1)]

end PolynomialVacuumBridge.Corridor

end

end OAI
