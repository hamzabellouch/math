import OAI.MeasureTheory.Falconer.Graphs.GraphAmplitudeScale
import OAI.MeasureTheory.Falconer.Geometry.DyadicClasses

namespace OAI

namespace PlanarFalconer

noncomputable def graphBinCountConstant (c₀ : ℝ) : ℝ := 4*Real.pi*max 1 c₀⁻¹

theorem graphBinCountConstant_nonneg (c₀ : ℝ) : 0 ≤ graphBinCountConstant c₀ := by
  dsimp [graphBinCountConstant]
  positivity

theorem graph_source_bin_count_le (N : ℕ) {sig t c₀ : ℝ} (hsig : 0 ≤ sig)
    (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) (ht : t ≤ (N:ℝ)) :
    (angularBinCount (graphAngularScale N sig t c₀) : ℝ) ≤ graphBinCountConstant c₀*(2:ℝ)^N := by
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hM : 1 ≤ max 1 c₀⁻¹ := le_max_left _ _
  have hunc : (graphUncappedAngularScale N sig t)⁻¹ ≤ (2:ℝ)^N := by
    rw [graphUncappedAngularScale,dyadic_power_real,← Real.rpow_add (by norm_num : (0:ℝ)<2),
      ← Real.rpow_neg_one,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    rw [← Real.rpow_natCast (2:ℝ) N]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_nonneg hsig (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hi : (graphAngularScale N sig t c₀)⁻¹ ≤ max 1 c₀⁻¹*(2:ℝ)^N := by
    unfold graphAngularScale
    by_cases hh : c₀ ≤ graphUncappedAngularScale N sig t
    · rw [min_eq_left hh]
      exact (le_max_right _ _).trans (le_mul_of_one_le_right (zero_le_one.trans hM) hR)
    · rw [min_eq_right (le_of_not_ge hh)]
      exact hunc.trans (le_mul_of_one_le_left (zero_le_one.trans hR) hM)
  have hb := (angularBinCount_bounds (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap)).2
  have he := (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mp hb
  calc
    _ ≤ (2 / graphAngularScale N sig t c₀) * (2*Real.pi) := he
    _ = 4*Real.pi*(graphAngularScale N sig t c₀)⁻¹ := by ring
    _ ≤ 4*Real.pi*(max 1 c₀⁻¹*(2:ℝ)^N) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by dsimp [graphBinCountConstant]; ring

abbrev GraphCellQuadIndex := (CellPath × CellPath) × (CellPath × CellPath)
abbrev GraphNonedgeIndex := GraphCellQuadIndex × ((ℕ × ℕ) × Bool)

def graphCellQuadIndices (p : ℕ) : Finset GraphCellQuadIndex :=
  ((dyadicPaths p).product (dyadicPaths p)).product ((dyadicPaths p).product (dyadicPaths p))

def graphNonedgeIndices (p n : ℕ) : Finset GraphNonedgeIndex :=
  (graphCellQuadIndices p).product (((Finset.range n).product (Finset.range n)).product Finset.univ)

theorem graph_cell_quad_count_le (N p : ℕ) (hp : p ≤ N) :
    ((graphCellQuadIndices p).card : ℝ) ≤ ((2:ℝ)^N)^8 := by
  have hc : ((dyadicPaths p).card : ℝ) ≤ (4:ℝ)^N := by
    exact_mod_cast (dyadicPaths_card_le p).trans (pow_le_pow_right₀ (by norm_num) hp)
  have he : (4:ℝ)^N = ((2:ℝ)^N)^2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,← pow_mul,← pow_mul,Nat.mul_comm 2 N]
  rw [he] at hc
  simp only [graphCellQuadIndices,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ (((2:ℝ)^N)^2*((2:ℝ)^N)^2)*(((2:ℝ)^N)^2*((2:ℝ)^N)^2) := by
      gcongr
    _ = _ := by ring

theorem graph_nonedge_index_count_le (N p n : ℕ) (hp : p ≤ N) {C : ℝ}
    (hC : 0 ≤ C) (hn : (n:ℝ) ≤ C*(2:ℝ)^N) :
    ((graphNonedgeIndices p n).card : ℝ) ≤ 2*C^2*((2:ℝ)^N)^10 := by
  have hq := graph_cell_quad_count_le N p hp
  simp only [graphNonedgeIndices,Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_bool,
    Finset.card_range,Nat.cast_mul,Nat.cast_ofNat]
  calc
    _ ≤ ((2:ℝ)^N)^8*((C*(2:ℝ)^N)*(C*(2:ℝ)^N)*2) := by
      gcongr
    _ = _ := by ring

end PlanarFalconer

end OAI
