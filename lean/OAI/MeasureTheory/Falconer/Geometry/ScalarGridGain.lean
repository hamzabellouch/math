import OAI.MeasureTheory.Falconer.Geometry.ScalarGridGainRates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! A strict projection gain for the full dyadic coefficient grid. The
sparse coefficient theorem needed for Furstenberg incidence is separate. -/
namespace Falconer
open Filter Real
open scoped Topology Pointwise

 theorem grid_gain_positive_margins {κ σ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/2) (hσ : σ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ 3*ε ≤ κ ∧ 4*ε ≤ 1-σ ∧
      8*ε ≤ (1-2*productInterpolationWeight κ)*(1-σ) := by
  obtain ⟨_,hθ,_,_⟩ := productInterpolationWeight_properties hκ hκ1
  let q := 1-2*productInterpolationWeight κ
  have hq : 0 < q := by dsimp [q]; linarith
  let ε := min (κ/4) (min ((1-σ)/8) (q*(1-σ)/16))
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have h₁ : ε ≤ κ/4 := min_le_left _ _
  have h₂ : ε ≤ (1-σ)/8 := (min_le_right _ _).trans (min_le_left _ _)
  have h₃ : ε ≤ q*(1-σ)/16 := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨ε,hε,by linarith,by linarith,by dsimp [q] at h₃; nlinarith⟩

 theorem small_scale_weight {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ,
      0 < δ → δ < δ₀ → D*δ^ε ≤ 1 := by
  have hlarge := (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hε)).eventually
    (eventually_ge_atTop D)
  obtain ⟨δ₀,hδ₀,hbound⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0 : ℝ) < 1 by norm_num)).mp hlarge
  refine ⟨min δ₀ 1,lt_min hδ₀ zero_lt_one,min_le_right _ _,?_⟩
  intro δ hδ hsmall
  have hb := hbound ⟨hδ,hsmall.trans_le (min_le_left _ _)⟩
  calc
    _ ≤ δ^(-ε)*δ^ε := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = 1 := by rw [← Real.rpow_add hδ]; simp

 theorem scalar_grid_projection_gain {κ σ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/2) (hσ : σ < 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ n : ℕ, 1/(2:ℝ)^n < δ₀ → ∀ X : Finset ℝ, X.Nonempty →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1/(2:ℝ)^n ≤ |x-y|) →
      (X.card : ℝ) ≤ (1/(2:ℝ)^n)^(-σ-ε) →
      (∀ u r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
        ((X.filter fun x => |x-u| ≤ r).card : ℝ) ≤
          (1/(2:ℝ)^n)^(-ε)*r^κ*(X.card : ℝ)) →
      ∃ c ∈ scalarDyadicGrid n,
        (1/(2:ℝ)^n)^(-ε)*(X.card : ℝ) ≤
          ((scalarCells (1/(2:ℝ)^n) (X+X.image (fun x => c*x))).card : ℝ) := by
  obtain ⟨ε,hε,hεκ,hεσ,hεθ⟩ := grid_gain_positive_margins hκ hκ1 hσ
  let θ := productInterpolationWeight κ
  let P := planarPotentialConstant 1 (1+κ/2)
  obtain ⟨δ₀,hδ₀,hδ₀1,hsmall⟩ := small_scale_weight hε (6+12*P*(1+81^θ))
  refine ⟨ε,δ₀,hε,hδ₀,hδ₀1,?_⟩
  intro n hn X hX hsep hupper hball
  let δ : ℝ := 1/(2:ℝ)^n
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := hn.le.trans hδ₀1
  have hN : 0 < (X.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
  obtain ⟨hθ,hθ1,_,_⟩ := productInterpolationWeight_properties hκ hκ1
  have hself : 1 ≤ δ^(κ-ε)*(X.card : ℝ) := by
    have hh := scalar_ball_self_bound hδ hδ1 X hX hball
    change 1 ≤ δ^(-ε)*δ^κ*(X.card : ℝ) at hh
    simpa only [← Real.rpow_add hδ,neg_add_eq_sub] using hh
  have hcount := grid_gain_count_rate hδ hδ1 hN hεκ hself
  obtain ⟨hvol,hvol'⟩ := grid_gain_volume_rate hδ hδ1 hεσ hε.le hupper
  have hweight := grid_gain_weight_rate hδ hδ1 hN hθ.le hθ1.le hε.le hεθ hvol'
  obtain ⟨c,hc,hproj⟩ := scalar_grid_large_projection n (by positivity : 0 ≤ δ^(-ε))
    hκ hκ1 X hX hsep hball
  refine ⟨c,hc,?_⟩
  exact grid_projection_gain_of_rates hδ hN
    (planarPotentialConstant_pos (show (1 : ℝ) < 1+κ/2 by linarith)).le
    hcount hvol hweight (hsmall δ hδ hn) hproj

end Falconer

end OAI
