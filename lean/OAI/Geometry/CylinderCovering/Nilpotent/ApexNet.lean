import OAI.Geometry.CylinderCovering.Nilpotent.ApexNetDefinitions

namespace OAI

open Set MeasureTheory

noncomputable section
namespace CylinderCovering.NilpotentApexNet

lemma meshCount_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < meshCount ρ :=
  Nat.ceil_pos.mpr (div_pos (by norm_num) hρ)

lemma step_le {ρ : ℝ} (hρ : 0 < ρ) : 2 / (meshCount ρ : ℝ) ≤ ρ := by
  have hm : (0 : ℝ) < meshCount ρ := by exact_mod_cast meshCount_pos hρ
  apply (div_le_iff₀ hm).2
  have hc := Nat.le_ceil (2 / ρ)
  change 2 / ρ ≤ (meshCount ρ : ℝ) at hc
  have := (div_le_iff₀ hρ).1 hc
  nlinarith

lemma count_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (meshCount ρ + 1 : ℕ) ≤ (4 / ρ : ℝ) := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 / ρ by positivity)
  change (meshCount ρ : ℝ) < 2 / ρ + 1 at hc
  have htwo : (2 : ℝ) ≤ 2 / ρ := (le_div_iff₀ hρ).2 (by linarith)
  push_cast
  have hid : 4 / ρ = 2 * (2 / ρ) := by ring
  linarith

lemma first_crossing {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) (z : ℝ)
    (h0 : f 0 ≤ z) (hN' : z ≤ f N) :
    ∃ j : ℕ, j < N ∧ f j ≤ z ∧ z ≤ f (j + 1) := by
  have hex : ∃ i : ℕ, 0 < i ∧ i ≤ N ∧ z ≤ f i := ⟨N, hN, le_rfl, hN'⟩
  let i := Nat.find hex
  have hi : 0 < i ∧ i ≤ N ∧ z ≤ f i := Nat.find_spec hex
  have him : i - 1 + 1 = i := by omega
  refine ⟨i - 1, by omega, ?_, by simpa [him] using hi.2.2⟩
  by_cases h : i = 1
  · simpa [h] using h0
  · have hsmall : i - 1 < Nat.find hex := by dsimp [i] at *; omega
    have hmin := Nat.find_min hex hsmall
    by_contra! hz
    exact hmin ⟨by omega, by omega, le_of_lt hz⟩

lemma node_bounds {ρ : ℝ} (hρ : 0 < ρ) {j : ℕ} (hj : j ≤ meshCount ρ) :
    |node ρ j| ≤ 1 := by
  have hm : (0 : ℝ) < meshCount ρ := by exact_mod_cast meshCount_pos hρ
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hjm : (j : ℝ) ≤ meshCount ρ := by exact_mod_cast hj
  rw [node, abs_le]
  constructor
  · have : 0 ≤ 2 * (j : ℝ) / meshCount ρ := by positivity
    linarith
  · have : 2 * (j : ℝ) / meshCount ρ ≤ 2 :=
      (div_le_iff₀ hm).2 (by linarith)
    linarith

lemma exists_near_node {ρ p : ℝ} (hρ : 0 < ρ) (hp : |p| ≤ 1) :
    ∃ j : Fin (meshCount ρ + 1), |p - node ρ j| ≤ ρ := by
  have hm := meshCount_pos hρ
  have hm0 : (meshCount ρ : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hfirst : node ρ 0 = -1 := by simp [node]
  have hlast : node ρ (meshCount ρ) = 1 := by
    unfold node
    field_simp
    ring
  obtain ⟨j, hj, hlo, hhi⟩ := first_crossing hm (node ρ) p
    (by rw [hfirst]; exact (abs_le.mp hp).1)
    (by rw [hlast]; exact (abs_le.mp hp).2)
  refine ⟨⟨j, by omega⟩, ?_⟩
  have hdiff : node ρ (j + 1) - node ρ j = 2 / meshCount ρ := by
    simp only [node, Nat.cast_add, Nat.cast_one]
    ring
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hs := step_le hρ
  change p - node ρ j ≤ ρ
  linarith

lemma v_lipschitz {p q : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    |(1 + p ^ 2) / 4 - (1 + q ^ 2) / 4| ≤ |p - q| / 2 := by
  have hadd : |p + q| ≤ 2 := (abs_add_le p q).trans (by linarith)
  rw [show (1 + p ^ 2) / 4 - (1 + q ^ 2) / 4 =
    (p - q) * (p + q) / 4 by ring, abs_div, abs_mul]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left hadd (abs_nonneg (p - q))]

lemma velocity_difference {k σ p q ρ : ℝ} (hk : 0 ≤ k) (hσ : |σ| ≤ 1)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hpq : |p - q| ≤ ρ) :
    |(velocity k σ p).1 - (velocity k σ q).1| ≤ k * ρ / 2 ∧
    |(velocity k σ p).2 - (velocity k σ q).2| ≤ k * ρ / 2 := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans hpq
  have hcoeff : |σ * k| ≤ k := by
    rw [abs_mul, abs_of_nonneg hk]
    simpa using mul_le_mul_of_nonneg_right hσ hk
  have hv : |(1 + p ^ 2) / 4 - (1 + q ^ 2) / 4| ≤ ρ / 2 :=
    (v_lipschitz hp hq).trans (by linarith)
  have hw : |p / 2 - q / 2| ≤ ρ / 2 := by
    rw [show p / 2 - q / 2 = (p - q) / 2 by ring, abs_div]
    norm_num
    linarith
  constructor
  · change |σ * k * ((1 + p ^ 2) / 4) - σ * k * ((1 + q ^ 2) / 4)| ≤ _
    rw [← mul_sub, abs_mul]
    have := mul_le_mul hcoeff hv (abs_nonneg _) hk
    nlinarith
  · change |σ * k * (p / 2) - σ * k * (q / 2)| ≤ _
    rw [← mul_sub, abs_mul]
    have := mul_le_mul hcoeff hw (abs_nonneg _) hk
    nlinarith

lemma residual_bound {k ρ σ p q s t : ℝ} (hk : 0 ≤ k) (hσ : |σ| ≤ 1)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hpq : |p - q| ≤ ρ)
    (hs : |s| ≤ 1) (ht : 0 ≤ t) (htρ : t ≤ ρ) :
    (p * t, t) + s • velocity k σ p - s • velocity k σ q ∈ tile k ρ := by
  have hρ := ht.trans htρ
  obtain ⟨hv, hw⟩ := velocity_difference hk hσ hp hq hpq
  have hpt : |p * t| ≤ ρ := by
    rw [abs_mul, abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_right hp ht).trans (by simpa using htρ)
  have hfirst : |p * t + s * ((velocity k σ p).1 - (velocity k σ q).1)| ≤ radius k ρ := by
    calc
      _ ≤ |p * t| + |s| * |(velocity k σ p).1 - (velocity k σ q).1| := by
        simpa only [abs_mul] using abs_add_le (p * t) (s * ((velocity k σ p).1 - (velocity k σ q).1))
      _ ≤ ρ + 1 * (k * ρ / 2) := add_le_add hpt (mul_le_mul hs hv (abs_nonneg _) (by norm_num))
      _ = radius k ρ := by unfold radius; ring
  have hsecond : |t + s * ((velocity k σ p).2 - (velocity k σ q).2)| ≤ radius k ρ := by
    calc
      _ ≤ |t| + |s| * |(velocity k σ p).2 - (velocity k σ q).2| := by
        simpa only [abs_mul] using abs_add_le t (s * ((velocity k σ p).2 - (velocity k σ q).2))
      _ ≤ ρ + 1 * (k * ρ / 2) := add_le_add (by rwa [abs_of_nonneg ht])
        (mul_le_mul hs hw (abs_nonneg _) (by norm_num))
      _ = radius k ρ := by unfold radius; ring
  change (-radius k ρ ≤ p * t + s * (velocity k σ p).1 - s * (velocity k σ q).1 ∧
    -radius k ρ ≤ t + s * (velocity k σ p).2 - s * (velocity k σ q).2) ∧
    (p * t + s * (velocity k σ p).1 - s * (velocity k σ q).1 ≤ radius k ρ ∧
    t + s * (velocity k σ p).2 - s * (velocity k σ q).2 ≤ radius k ρ)
  rw [abs_le] at hfirst hsecond
  constructor <;> constructor <;> nlinarith only [hfirst.1, hfirst.2, hsecond.1, hsecond.2]

theorem apex_cover {k ρ σ : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ) (hσ : |σ| ≤ 1) :
    apexSweep k ρ σ ⊆ ⋃ j : Fin (meshCount ρ + 1), cylinder k ρ σ j := by
  rintro z ⟨s, p, t, hs, hp, ht, htρ, rfl⟩
  obtain ⟨j, hj⟩ := exists_near_node hρ hp
  refine mem_iUnion.mpr ⟨j, ?_⟩
  exact residual_bound hk hσ hp (node_bounds hρ (by omega)) hj hs ht htρ

lemma weight_bounds (h : ℝ) (g : ℝ × ℝ) : 0 ≤ weight h g ∧ weight h g ≤ 1 := by
  have hrad : 1 ≤ 1 + g.1 ^ 2 + h ^ 2 * g.2 ^ 2 := by nlinarith [sq_nonneg g.1, mul_nonneg (sq_nonneg h) (sq_nonneg g.2)]
  have hsqrt : 1 ≤ Real.sqrt (1 + g.1 ^ 2 + h ^ 2 * g.2 ^ 2) := Real.one_le_sqrt.mpr hrad
  unfold weight
  exact ⟨by positivity, (div_le_one (by linarith)).2 hsqrt⟩

lemma tile_area {k ρ : ℝ} (hk : 0 ≤ k) (hρ : 0 ≤ ρ) :
    (volume (tile k ρ)).toReal = 4 * (radius k ρ) ^ 2 := by
  have hr : 0 ≤ radius k ρ := by unfold radius; positivity
  unfold tile
  rw [Icc_prod_eq]
  change ((volume.prod volume) (Icc (-radius k ρ) (radius k ρ) ×ˢ
    Icc (-radius k ρ) (radius k ρ))).toReal = _
  rw [Measure.prod_prod, Real.volume_Icc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ radius k ρ - -radius k ρ)]
  ring

theorem apex_cost {k ρ σ : ℝ} (h : ℝ) (hk : 0 ≤ k) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (∑ j : Fin (meshCount ρ + 1), weightedArea h k ρ σ j) ≤
      16 * (1 + k / 2) ^ 2 * ρ := by
  have hcost : ∀ j : Fin (meshCount ρ + 1), weightedArea h k ρ σ j ≤ 4 * (radius k ρ) ^ 2 := by
    intro j
    unfold weightedArea
    rw [tile_area hk hρ.le]
    exact (mul_le_mul_of_nonneg_left (weight_bounds h _).2 (by positivity)).trans_eq (by ring)
  calc
    _ ≤ ∑ _j : Fin (meshCount ρ + 1), 4 * (radius k ρ) ^ 2 := Finset.sum_le_sum (fun j _ => hcost j)
    _ = (meshCount ρ + 1 : ℕ) * (4 * (radius k ρ) ^ 2) := by simp
    _ ≤ (4 / ρ) * (4 * (radius k ρ) ^ 2) :=
      mul_le_mul_of_nonneg_right (count_bound hρ hρ1) (by positivity)
    _ = 16 * (1 + k / 2) ^ 2 * ρ := by
      unfold radius
      field_simp
      ring

lemma tile_compact (k ρ : ℝ) : IsCompact (tile k ρ) := isCompact_Icc

lemma tile_convex (k ρ : ℝ) : Convex ℝ (tile k ρ) := convex_Icc _ _

lemma tile_measurable (k ρ : ℝ) : MeasurableSet (tile k ρ) := measurableSet_Icc

lemma radius_pos {k ρ : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ) : 0 < radius k ρ := by
  unfold radius
  positivity

lemma tile_area_pos {k ρ : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ) :
    0 < (volume (tile k ρ)).toReal := by
  rw [tile_area hk hρ.le]
  exact mul_pos (by norm_num) (sq_pos_of_pos (radius_pos hk hρ))

theorem apexNet {k ρ σ : ℝ} (h : ℝ) (hk : 0 ≤ k) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hσ : |σ| ≤ 1) :
    IsCompact (tile k ρ) ∧ Convex ℝ (tile k ρ) ∧ MeasurableSet (tile k ρ) ∧
    0 < (volume (tile k ρ)).toReal ∧
    (volume (tile k ρ)).toReal = (2 * (1 + k / 2) * ρ) ^ 2 ∧
    (meshCount ρ + 1 : ℕ) ≤ (4 / ρ : ℝ) ∧
    apexSweep k ρ σ ⊆ ⋃ j : Fin (meshCount ρ + 1), cylinder k ρ σ j ∧
    (∑ j : Fin (meshCount ρ + 1), weightedArea h k ρ σ j) ≤
      16 * (1 + k / 2) ^ 2 * ρ := by
  refine ⟨tile_compact k ρ, tile_convex k ρ, tile_measurable k ρ,
    tile_area_pos hk hρ, ?_, count_bound hρ hρ1, apex_cover hk hρ hσ,
    apex_cost h hk hρ hρ1⟩
  rw [tile_area hk hρ.le]
  unfold radius
  ring

theorem auxiliaryApexNet : AuxiliaryApexNetStatement := by
  intro h k ρ σ hk hρ hρ1 hσ
  exact apexNet h hk hρ hρ1 hσ

end CylinderCovering.NilpotentApexNet

end

end OAI
