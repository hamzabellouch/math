import Mathlib

namespace OAI

open Set
open scoped NNReal

namespace CylinderCovering.ThresholdInversion

section Normed

variable {E : Type*} [NormedAddCommGroup E]

theorem inverse_distance_bound {g : E → E} {p q y z : E} {c : ℝ}
    (hc : c < 1) (hgp : p + g p = y) (hgq : q + g q = z)
    (hlip : ‖g q - g p‖ ≤ c * ‖q - p‖) :
    ‖q - p‖ ≤ ‖z - y‖ / (1 - c) := by
  have heq : q - p = (z - y) - (g q - g p) := by
    rw [← hgp, ← hgq]
    abel
  have htriangle := norm_sub_le (z - y) (g q - g p)
  rw [← heq] at htriangle
  apply (le_div_iff₀ (by linarith : 0 < 1 - c)).2
  nlinarith

theorem inverse_displacement_error {g : E → E} {p q y z : E} {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < 1) (hgp : p + g p = y) (hgq : q + g q = z)
    (hlip : ‖g q - g p‖ ≤ c * ‖q - p‖) :
    ‖(q - p) - (z - y)‖ ≤ c / (1 - c) * ‖z - y‖ := by
  have heq : (q - p) - (z - y) = -(g q - g p) := by
    rw [← hgp, ← hgq]
    abel
  rw [heq, norm_neg]
  calc
    ‖g q - g p‖ ≤ c * ‖q - p‖ := hlip
    _ ≤ c * (‖z - y‖ / (1 - c)) :=
      mul_le_mul_of_nonneg_left (inverse_distance_bound hc hgp hgq hlip) hc0
    _ = c / (1 - c) * ‖z - y‖ := by ring

theorem inverse_unique {g : E → E} {p q y : E} {c : ℝ}
    (hc : c < 1) (hgp : p + g p = y) (hgq : q + g q = y)
    (hlip : ‖g q - g p‖ ≤ c * ‖q - p‖) : p = q := by
  have h := inverse_distance_bound hc hgp hgq hlip
  simp only [sub_self, norm_zero, zero_div] at h
  have hzero : q - p = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  exact (sub_eq_zero.mp hzero).symm

theorem existsUnique_inverse_on {s : Set E} (hs : IsComplete s) (hsne : s.Nonempty)
    {g : E → E} {c : ℝ≥0} (hc : c < 1) (hlip : LipschitzOnWith c g s)
    (y : E) (hmaps : MapsTo (fun p => y - g p) s s) :
    ∃! p : E, p ∈ s ∧ p + g p = y := by
  let f : E → E := fun p => y - g p
  have hf : ContractingWith c (hmaps.restrict f s s) := by
    refine ⟨hc, LipschitzWith.of_dist_le_mul ?_⟩
    intro p q
    change dist (y - g p) (y - g q) ≤ (c : ℝ) * dist (p : E) (q : E)
    rw [dist_sub_left]
    exact hlip.dist_le_mul p p.property q q.property
  obtain ⟨p₀, hp₀⟩ := hsne
  obtain ⟨p, hps, hfix, _⟩ :=
    ContractingWith.exists_fixedPoint' hs hmaps hf hp₀ (edist_ne_top _ _)
  have hpeq : p + g p = y := by
    have hfix' : y - g p = p := hfix
    calc
      p + g p = (y - g p) + g p := congrArg (fun v => v + g p) hfix'.symm
      _ = y := sub_add_cancel _ _
  refine ⟨p, ⟨hps, hpeq⟩, ?_⟩
  intro q hq
  apply inverse_unique (show (c : ℝ) < 1 by exact_mod_cast hc) hq.2 hpeq
  simpa only [dist_eq_norm] using hlip.dist_le_mul p hps q hq.1

end Normed

section Height

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverse_height_strict {g : E → E} {p q y z : E} {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < 1 / 2)
    (hgp : p + g p = y) (hgq : q + g q = z)
    (hlip : ‖g q - g p‖ ≤ c * ‖q - p‖)
    (height : E →ₗ[ℝ] ℝ) (hheight : ∀ v, |height v| ≤ ‖v‖)
    (hvertical : ‖z - y‖ = height z - height y)
    (hup : height y < height z) : height p < height q := by
  have hc1 : c < 1 := by linarith
  have hratio : c / (1 - c) < 1 := by
    apply (div_lt_one (by linarith : 0 < 1 - c)).2
    linarith
  have herr := inverse_displacement_error hc0 hc1 hgp hgq hlip
  have hsmall : ‖(q - p) - (z - y)‖ < height z - height y := by
    calc
      ‖(q - p) - (z - y)‖ ≤ c / (1 - c) * ‖z - y‖ := herr
      _ < height z - height y := by
        rw [hvertical]
        nlinarith
  have hcoord := hheight ((q - p) - (z - y))
  simp only [map_sub] at hcoord
  have hlower := (abs_le.mp hcoord).1
  linarith

end Height

section Euclidean

variable {n : Type*} [Fintype n]

omit [Fintype n] in

theorem box_iteration_mapsTo (lo hi margin : n → ℝ)
    (g : EuclideanSpace ℝ n → EuclideanSpace ℝ n) (y : EuclideanSpace ℝ n)
    (hbound : ∀ p, (∀ i, p i ∈ Icc (lo i) (hi i)) → ∀ i, |g p i| ≤ margin i)
    (hmargin : ∀ i, lo i + margin i ≤ y i ∧ y i ≤ hi i - margin i) :
    MapsTo (fun p => y - g p)
      {p | ∀ i, p i ∈ Icc (lo i) (hi i)}
      {p | ∀ i, p i ∈ Icc (lo i) (hi i)} := by
  intro p hp i
  have hb := abs_le.mp (hbound p hp i)
  have hm := hmargin i
  change lo i ≤ y i - g p i ∧ y i - g p i ≤ hi i
  constructor <;> linarith

theorem existsUnique_inverse_on_box (lo hi margin : n → ℝ)
    (hmargin0 : ∀ i, 0 ≤ margin i)
    {g : EuclideanSpace ℝ n → EuclideanSpace ℝ n} {c : ℝ≥0}
    (hc : c < 1)
    (hlip : LipschitzOnWith c g {p | ∀ i, p i ∈ Icc (lo i) (hi i)})
    (hbound : ∀ p, (∀ i, p i ∈ Icc (lo i) (hi i)) → ∀ i, |g p i| ≤ margin i)
    (y : EuclideanSpace ℝ n)
    (hmargin : ∀ i, lo i + margin i ≤ y i ∧ y i ≤ hi i - margin i) :
    ∃! p : EuclideanSpace ℝ n, (∀ i, p i ∈ Icc (lo i) (hi i)) ∧ p + g p = y := by
  have hclosed : IsClosed {p : EuclideanSpace ℝ n | ∀ i, p i ∈ Icc (lo i) (hi i)} := by
    have heq : {p : EuclideanSpace ℝ n | ∀ i, p i ∈ Icc (lo i) (hi i)} =
        ⋂ i, {p : EuclideanSpace ℝ n | p i ∈ Icc (lo i) (hi i)} := by
      ext p
      simp
    rw [heq]
    exact isClosed_iInter fun i => isClosed_Icc.preimage (by fun_prop)
  have hy : ∀ i, y i ∈ Icc (lo i) (hi i) := by
    intro i
    have hm := hmargin i
    have hm0 := hmargin0 i
    constructor <;> linarith
  exact existsUnique_inverse_on hclosed.isComplete ⟨y, hy⟩ hc hlip y
    (box_iteration_mapsTo lo hi margin g y hbound hmargin)

theorem existsUnique_inverse_on_box_smul (lo hi : n → ℝ) {margin : ℝ}
    (hmargin0 : 0 ≤ margin)
    {W : EuclideanSpace ℝ n → EuclideanSpace ℝ n} {L B t : ℝ}
    (hL : 0 ≤ L) (_hB : 0 ≤ B)
    (hlip : ∀ p, (∀ i, p i ∈ Icc (lo i) (hi i)) →
      ∀ q, (∀ i, q i ∈ Icc (lo i) (hi i)) → ‖W p - W q‖ ≤ L * ‖p - q‖)
    (hbound : ∀ p, (∀ i, p i ∈ Icc (lo i) (hi i)) → ‖W p‖ ≤ B)
    (htL : |t| * L < 1) (htB : |t| * B ≤ margin)
    (y : EuclideanSpace ℝ n)
    (hy : ∀ i, lo i + margin ≤ y i ∧ y i ≤ hi i - margin) :
    ∃! p : EuclideanSpace ℝ n,
      (∀ i, p i ∈ Icc (lo i) (hi i)) ∧ p + t • W p = y := by
  let c : ℝ≥0 := ⟨|t| * L, mul_nonneg (abs_nonneg _) hL⟩
  apply existsUnique_inverse_on_box lo hi (fun _ => margin) (fun _ => hmargin0)
    (c := c) (show c < 1 from htL) ?_ ?_ y hy
  · apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    change dist (t • W p) (t • W q) ≤ (|t| * L) * dist p q
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
    calc
      |t| * ‖W p - W q‖ ≤ |t| * (L * ‖p - q‖) :=
        mul_le_mul_of_nonneg_left (hlip p hp q hq) (abs_nonneg _)
      _ = |t| * L * ‖p - q‖ := by ring
  · intro p hp i
    calc
      |(t • W p) i| ≤ ‖t • W p‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (t • W p) i
      _ = |t| * ‖W p‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hbound p hp) (abs_nonneg _)
      _ ≤ margin := htB

theorem exists_small_tilt (L B margin : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hm : 0 < margin) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → |t| * L < 1 / 2 ∧ |t| * B ≤ margin := by
  let δ := min (1 / (2 * (L + 1))) (margin / (B + 1))
  have hLp : 0 < 2 * (L + 1) := by positivity
  have hBp : 0 < B + 1 := by positivity
  refine ⟨δ, lt_min (div_pos (by norm_num) hLp) (div_pos hm hBp), ?_⟩
  intro t ht
  have htL : |t| * (2 * (L + 1)) < 1 :=
    (lt_div_iff₀ hLp).mp (lt_of_lt_of_le ht (min_le_left _ _))
  have htB : |t| * (B + 1) < margin :=
    (lt_div_iff₀ hBp).mp (lt_of_lt_of_le ht (min_le_right _ _))
  constructor <;> nlinarith [abs_nonneg t]

theorem inverse_coordinate_strict {g : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
    {p q y z : EuclideanSpace ℝ n} {c : ℝ} (i : n)
    (hc0 : 0 ≤ c) (hc : c < 1 / 2)
    (hgp : p + g p = y) (hgq : q + g q = z)
    (hlip : ‖g q - g p‖ ≤ c * ‖q - p‖)
    (hvertical : ∀ j, j ≠ i → z j = y j) (hup : y i < z i) : p i < q i := by
  classical
  apply inverse_height_strict hc0 hc hgp hgq hlip (PiLp.projₗ 2 (fun _ : n => ℝ) i)
  · intro v
    exact PiLp.norm_apply_le v i
  · have heq : z - y = PiLp.single 2 i (z i - y i) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji, hvertical j hji]
    rw [heq, PiLp.norm_single]
    exact abs_of_pos (sub_pos.mpr hup)
  · exact hup

end Euclidean

end CylinderCovering.ThresholdInversion

end OAI
