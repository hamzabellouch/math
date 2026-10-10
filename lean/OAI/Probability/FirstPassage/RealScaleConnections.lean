import OAI.Probability.FirstPassage.UniformShape
import Mathlib.Topology.Instances.Int

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

lemma latticeEmbed_norm_le_of_box (p : Vertex) (n : ℕ) (hp : p ∈ latticeBox n) :
    ‖latticeEmbed p‖ ≤ 2*(n : ℝ) := by
  have h := Finset.mem_product.mp hp
  have h₁ := Finset.mem_Icc.mp h.1
  have h₂ := Finset.mem_Icc.mp h.2
  have h₁' : |(p.1 : ℝ)| ≤ n := by exact_mod_cast (abs_le.mpr h₁)
  have h₂' : |(p.2 : ℝ)| ≤ n := by exact_mod_cast (abs_le.mpr h₂)
  exact (plane_norm_le_coordinates _).trans (by simpa [latticeEmbed,two_mul] using add_le_add h₁' h₂')

lemma lattice_mem_box_of_norm (p : Vertex) (n : ℕ) (hp : ‖latticeEmbed p‖ ≤ n) :
    p ∈ latticeBox n := by
  have hi (i : Fin 2) := (plane_coordinate_le_norm (latticeEmbed p) i).trans hp
  have h₁ : |p.1| ≤ (n : ℤ) := by exact_mod_cast (show |(p.1 : ℝ)| ≤ n from hi 0)
  have h₂ : |p.2| ≤ (n : ℤ) := by exact_mod_cast (show |(p.2 : ℝ)| ≤ n from hi 1)
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp h₁),Finset.mem_Icc.mpr (abs_le.mp h₂)⟩

theorem real_scale_connections (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < 4*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ p q : Vertex,
      ‖latticeEmbed p‖ ≤ C*t → ‖latticeEmbed q‖ ≤ C*t →
      |passageTime w 0 p/t-passageTime w 0 q/t| ≤
        4*(latticeDistance p q : ℝ)/t+ε := by
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (div_pos hε (show 0 < C+1 by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hc k)
  filter_upwards [eventually_ge_atTop (max 1 ((N : ℝ)/C))] with t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  let n : ℕ := ⌈C*t⌉₊
  have htn : C*t ≤ (n : ℝ) := Nat.le_ceil _
  have hnu : (n : ℝ) ≤ (C+1)*t := by
    have he := Nat.ceil_lt_add_one (show 0 ≤ C*t by positivity)
    dsimp [n]
    nlinarith
  have hnN : N ≤ n := by
    have hh := (div_le_iff₀ hC).mp ((le_max_right _ _).trans ht)
    have hh' : (N : ℝ) ≤ (n : ℝ) := by nlinarith
    exact_mod_cast hh'
  intro p q hp hq
  have hp' := lattice_mem_box_of_norm p n (hp.trans htn)
  have hq' := lattice_mem_box_of_norm q n (hq.trans htn)
  have hdiff := passageTime_origin_difference_le w hw p q
  have hconn := hN n hnN p hp' q hq'
  have he : (1/(k+1 : ℝ))*(n : ℝ) ≤ ε*t := by
    have ha := mul_le_mul_of_nonneg_left hnu (show 0 ≤ 1/(k+1 : ℝ) by positivity)
    have hb := (lt_div_iff₀ (show 0 < C+1 by linarith)).mp hk
    nlinarith
  rw [← sub_div,abs_div,abs_of_pos ht0]
  apply (div_le_iff₀ ht0).mpr
  rw [add_mul,div_mul_cancel₀ _ ht0.ne']
  linarith

lemma floor_real_ratio_tendsto (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => (⌊t/M⌋₊ : ℝ)/t) atTop (𝓝 (1/M)) := by
  simpa [div_eq_mul_inv,mul_comm] using
    (tendsto_nat_floor_mul_div_atTop (inv_nonneg.mpr hM.le))

noncomputable def scaledLatticePoint (t : ℝ) (p : Vertex) : Plane :=
  (1/t) • latticeEmbed p

lemma scaledLatticePoint_norm (t : ℝ) (ht : 0 < t) (p : Vertex) :
    ‖scaledLatticePoint t p‖ = ‖latticeEmbed p‖/t := by
  rw [scaledLatticePoint,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ht)]
  ring

lemma scaledLatticePoint_sub_norm (t : ℝ) (ht : 0 < t) (p q : Vertex) :
    ‖scaledLatticePoint t p-scaledLatticePoint t q‖ = ‖latticeEmbed p-latticeEmbed q‖/t := by
  rw [scaledLatticePoint,scaledLatticePoint,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr ht)]
  ring

lemma scaled_floor_error (t : ℝ) (ht : 0 < t) (v : Plane) :
    ‖scaledLatticePoint t (latticeFloor (t • v))-v‖ ≤ 2/t := by
  have he : scaledLatticePoint t (latticeFloor (t • v))-v =
      (1/t) • (latticeEmbed (latticeFloor (t • v))-t • v) := by
    rw [smul_sub,smul_smul,one_div_mul_cancel ht.ne',one_smul]
    rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ht)]
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using
    mul_le_mul_of_nonneg_left (latticeFloor_error (t • v)) (le_of_lt (one_div_pos.mpr ht))

lemma scaled_floor_tendsto (v : Plane) :
    Tendsto (fun t : ℝ => scaledLatticePoint t (latticeFloor (t • v))) atTop (𝓝 v) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (max 0 (2/ε))] with t ht
  have ht0 : 0 < t := (le_max_left _ _).trans_lt ht
  rw [dist_eq_norm]
  exact (scaled_floor_error t ht0 v).trans_lt ((div_lt_iff₀ ht0).mpr
    (by have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt ht); nlinarith))

lemma latticeEmbed_nsmul (n : ℕ) (z : Vertex) :
    latticeEmbed (n • z) = (n : ℝ) • latticeEmbed z := by
  ext i
  fin_cases i <;> simp [latticeEmbed,nsmul_eq_mul]

lemma scaled_lattice_ray_tendsto (z : Vertex) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => scaledLatticePoint t (⌊t/M⌋₊ • z)) atTop
      (𝓝 ((1/M) • latticeEmbed z)) := by
  have h := (floor_real_ratio_tendsto M hM).smul_const (latticeEmbed z)
  simpa only [scaledLatticePoint,latticeEmbed_nsmul,smul_smul,one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h

theorem real_scale_connections_normalized (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < 4*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ p q : Vertex,
      ‖scaledLatticePoint t p‖ ≤ C → ‖scaledLatticePoint t q‖ ≤ C →
      |passageTime w 0 p/t-passageTime w 0 q/t| ≤
        8*‖scaledLatticePoint t p-scaledLatticePoint t q‖+ε := by
  filter_upwards [real_scale_connections w hw hc C hC ε hε,
    eventually_gt_atTop (0 : ℝ)] with t ht ht0
  intro p q hp hq
  rw [scaledLatticePoint_norm t ht0] at hp hq
  have he := ht p q ((div_le_iff₀ ht0).mp hp) ((div_le_iff₀ ht0).mp hq)
  have hd := latticeDistance_le_norm p q
  rw [norm_sub_rev] at hd
  rw [scaledLatticePoint_sub_norm t ht0]
  apply he.trans
  have hh := (div_le_div_of_nonneg_right hd ht0.le)
  simp only [mul_div_assoc] at hh ⊢
  linarith

end PlanarFPP

end OAI
