import Mathlib
import OAI.Analysis.MatrixSigning.Potential.LightPoint
import OAI.Analysis.MatrixSigning.Realization.NaturalRealization
import OAI.Analysis.MatrixSigning.Realization.ScalarRealization
import OAI.Combinatorics.ThinTrees.ShortcutDuality

namespace OAI

/-! Metric profiles. -/

section

noncomputable section

namespace AlgorithmicThinTrees.MetricProfiles

open Finset Set

section Profiles

variable {V : Type*} [Fintype V] [PseudoMetricSpace V]

def profile (x : V) : V → ℝ := fun z => dist x z

def polytope : Set (V → ℝ) := convexHull ℝ (Set.range (profile (V := V)))

omit [Fintype V] in
lemma profile_mem (x : V) : profile x ∈ polytope :=
  subset_convexHull ℝ _ (Set.mem_range_self x)

omit [Fintype V] in
lemma polytope_convex : Convex ℝ (polytope (V := V)) := convex_convexHull ℝ _

lemma polytope_compact : IsCompact (polytope (V := V)) :=
  (Set.finite_range (profile (V := V))).isCompact_convexHull ℝ

lemma profile_norm_sub (x y : V) : ‖profile x - profile y‖ = dist x y := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg dist_nonneg).2
    intro z
    simp only [Pi.sub_apply, profile, Real.norm_eq_abs]
    apply abs_sub_le_iff.2
    constructor
    · linarith [dist_triangle x y z]
    · have h := dist_triangle y x z
      rw [dist_comm y x] at h
      linarith
  · have h := norm_le_pi_norm (profile x - profile y) y
    simpa [profile, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using h

lemma profile_isometry : Isometry (profile (V := V)) :=
  Isometry.of_dist_eq fun x y => by rw [dist_eq_norm, profile_norm_sub]

omit [PseudoMetricSpace V] in
lemma norm_coordinate_convex (c : V → ℝ) (i : V) :
    Convex ℝ {x : V → ℝ | ‖x - c‖ ≤ x i} := by
  intro x hx y hy a b ha hb hab
  change ‖a • x + b • y - c‖ ≤ (a • x + b • y) i
  have heq : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination c j * hab
  rw [heq]
  calc
    ‖a • (x - c) + b • (y - c)‖ ≤ ‖a • (x - c)‖ + ‖b • (y - c)‖ := norm_add_le _ _
    _ = a * ‖x - c‖ + b * ‖y - c‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * x i + b * y i := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = (a • x + b • y) i := rfl

theorem radius_eq_coordinate {q : V → ℝ} (hq : q ∈ polytope) (x : V) :
    ‖q - profile x‖ = q x := by
  have hupper : ‖q - profile x‖ ≤ q x := by
    apply convexHull_min (t := {y : V → ℝ | ‖y - profile x‖ ≤ y x}) ?_
      (norm_coordinate_convex (profile x) x) hq
    rintro _ ⟨y, rfl⟩
    exact (profile_norm_sub y x).le
  have hlower : q x ≤ ‖q - profile x‖ := by
    have h := norm_le_pi_norm (q - profile x) x
    simp only [Pi.sub_apply, profile, dist_self, sub_zero, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  exact le_antisymm hupper hlower

lemma coordinate_nonneg {q : V → ℝ} (hq : q ∈ polytope) (x : V) : 0 ≤ q x := by
  rw [← radius_eq_coordinate hq x]
  exact norm_nonneg _

end Profiles

section Double

variable (V : Type*) [Fintype V] [PseudoMetricSpace V]

def commonRadius : ℝ := 1 + 2 * ∑ x : V, ∑ y : V, dist x y

lemma commonRadius_pos : 0 < commonRadius V := by
  have h : 0 ≤ ∑ x : V, ∑ y : V, dist x y :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => dist_nonneg
  unfold commonRadius
  linarith

lemma twice_dist_lt_commonRadius (x y : V) : 2 * dist x y < commonRadius V := by
  have h₁ : dist x y ≤ ∑ z : V, dist x z :=
    single_le_sum (fun z _ => (dist_nonneg : (0 : ℝ) ≤ dist x z)) (mem_univ y)
  have h₂ : (∑ z : V, dist x z) ≤ ∑ u : V, ∑ z : V, dist u z :=
    single_le_sum (fun u _ => sum_nonneg fun z _ =>
      (dist_nonneg : (0 : ℝ) ≤ dist u z)) (mem_univ x)
  unfold commonRadius
  linarith

@[ext]
structure Doubled where
  sign : Bool
  point : V
  deriving Fintype

variable {V}

def doubledDist (a b : Doubled V) : ℝ :=
  if a.sign = b.sign then dist a.point b.point
  else commonRadius V - dist a.point b.point

lemma doubledDist_self (a : Doubled V) : doubledDist a a = 0 := by
  simp [doubledDist]

lemma doubledDist_comm (a b : Doubled V) : doubledDist a b = doubledDist b a := by
  simp only [doubledDist, eq_comm, dist_comm]

lemma doubledDist_triangle (a b c : Doubled V) :
    doubledDist a c ≤ doubledDist a b + doubledDist b c := by
  have hab := twice_dist_lt_commonRadius V a.point b.point
  have hbc := twice_dist_lt_commonRadius V b.point c.point
  have hac := twice_dist_lt_commonRadius V a.point c.point
  have hR := commonRadius_pos V
  have h₁ := dist_triangle a.point b.point c.point
  have h₂ := dist_triangle a.point c.point b.point
  have h₃ := dist_triangle b.point a.point c.point
  rw [dist_comm c.point b.point] at h₂
  rw [dist_comm b.point a.point] at h₃
  rcases a with ⟨a, x⟩
  rcases b with ⟨b, y⟩
  rcases c with ⟨c, z⟩
  cases a <;> cases b <;> cases c <;>
    simp_all only [doubledDist, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte] <;> linarith

instance : PseudoMetricSpace (Doubled V) where
  dist := doubledDist
  dist_self := doubledDist_self
  dist_comm := doubledDist_comm
  dist_triangle := doubledDist_triangle

def plus (x : V) : Doubled V := ⟨true, x⟩
def minus (x : V) : Doubled V := ⟨false, x⟩

lemma dist_plus (x y : V) : dist (plus x) (plus y) = dist x y := by
  change doubledDist _ _ = _
  simp [doubledDist, plus]

lemma dist_minus (x y : V) : dist (minus x) (minus y) = dist x y := by
  change doubledDist _ _ = _
  simp [doubledDist, minus]

lemma opposite_dist (x : V) : dist (plus x) (minus x) = commonRadius V := by
  change doubledDist _ _ = _
  simp [doubledDist, plus, minus]

lemma profile_opposite_sum (x : V) (a : Doubled V) :
    profile a (plus x) + profile a (minus x) = commonRadius V := by
  change doubledDist a _ + doubledDist a _ = _
  rcases a with ⟨s, y⟩
  cases s <;> simp [doubledDist, plus, minus]

lemma opposite_coordinate_sum {q : Doubled V → ℝ}
    (hq : q ∈ polytope) (x : V) : q (plus x) + q (minus x) = commonRadius V := by
  have hconv : Convex ℝ {q : Doubled V → ℝ |
      q (plus x) + q (minus x) = commonRadius V} := by
    intro q hq r hr a b _ _ hab
    change (a • q + b • r) (plus x) + (a • q + b • r) (minus x) = _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change q (plus x) + q (minus x) = commonRadius V at hq
    change r (plus x) + r (minus x) = commonRadius V at hr
    calc
      _ = a * (q (plus x) + q (minus x)) +
          b * (r (plus x) + r (minus x)) := by ring
      _ = a * commonRadius V + b * commonRadius V := by rw [hq, hr]
      _ = commonRadius V := by rw [← add_mul, hab, one_mul]
  exact convexHull_min (by rintro _ ⟨a, rfl⟩; exact profile_opposite_sum x a) hconv hq

theorem opposite_radii {q : Doubled V → ℝ} (hq : q ∈ polytope) (x : V) :
    ‖q - profile (plus x)‖ + ‖q - profile (minus x)‖ = commonRadius V := by
  rw [radius_eq_coordinate hq, radius_eq_coordinate hq]
  exact opposite_coordinate_sum hq x

theorem original_isometry : Isometry (fun x : V => profile (plus x)) :=
  Isometry.of_dist_eq fun x y => by rw [dist_eq_norm, profile_norm_sub, dist_plus]

end Double

section Segments

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def mix (q r : E) (t : ℝ) : E := (1 - t) • q + t • r

@[simp] lemma mix_zero (q r : E) : mix q r 0 = q := by simp [mix]
@[simp] lemma mix_one (q r : E) : mix q r 1 = r := by simp [mix]

lemma mix_sub_mix (q r : E) (t s : ℝ) :
    mix q r t - mix q r s = (t - s) • (r - q) := by
  unfold mix
  module

lemma segment_distance (q r : E) (t s : ℝ) :
    ‖mix q r t - mix q r s‖ = |t - s| * ‖r - q‖ := by
  rw [mix_sub_mix, norm_smul, Real.norm_eq_abs]

theorem segment_subdivision_length (q r : E) (N : ℕ) (t : ℕ → ℝ)
    (ht : ∀ i < N, t i ≤ t (i + 1)) (hzero : t 0 = 0) (hone : t N = 1) :
    ∑ i ∈ Finset.range N, ‖mix q r (t (i + 1)) - mix q r (t i)‖ = ‖r - q‖ := by
  have hsum : (∑ i ∈ Finset.range N, (t (i + 1) - t i)) = 1 := by
    rw [Finset.sum_range_sub, hone, hzero, sub_zero]
  calc
    _ = ∑ i ∈ Finset.range N, (t (i + 1) - t i) * ‖r - q‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [segment_distance, abs_of_nonneg (sub_nonneg.mpr (ht i (mem_range.mp hi)))]
    _ = (∑ i ∈ Finset.range N, (t (i + 1) - t i)) * ‖r - q‖ :=
      (Finset.sum_mul _ _ _).symm
    _ = ‖r - q‖ := by rw [hsum, one_mul]

end Segments

section RadialMotion

variable {V : Type*} [Fintype V] [PseudoMetricSpace V]

lemma mix_mem {q r : V → ℝ} (hq : q ∈ polytope) (hr : r ∈ polytope)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : mix q r t ∈ polytope :=
  polytope_convex hq hr (sub_nonneg.mpr ht.2) ht.1 (by ring)

lemma radius_mix {q r : V → ℝ} (hq : q ∈ polytope) (hr : r ∈ polytope)
    (x : V) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖mix q r t - profile x‖ = (1 - t) * ‖q - profile x‖ + t * ‖r - profile x‖ := by
  rw [radius_eq_coordinate (mix_mem hq hr ht), radius_eq_coordinate hq,
    radius_eq_coordinate hr]
  rfl

lemma inward_radius {q : Doubled V → ℝ} (hq : q ∈ polytope)
    (x : V) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖mix q (profile (plus x)) t - profile (plus x)‖ =
      (1 - t) * ‖q - profile (plus x)‖ := by
  rw [radius_mix hq (profile_mem _) _ ht]
  simp

lemma inward_distance (q : Doubled V → ℝ) (x : V) {t : ℝ} (ht : 0 ≤ t) :
    ‖mix q (profile (plus x)) t - q‖ = t * ‖q - profile (plus x)‖ := by
  simpa only [mix_zero, sub_zero, abs_of_nonneg ht, norm_sub_rev (profile (plus x)) q]
    using segment_distance q (profile (plus x)) t 0

lemma outward_radius {q : Doubled V → ℝ} (hq : q ∈ polytope)
    (x : V) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖mix q (profile (minus x)) t - profile (plus x)‖ =
      ‖q - profile (plus x)‖ + t * (commonRadius V - ‖q - profile (plus x)‖) := by
  rw [radius_mix hq (profile_mem _) _ ht, profile_norm_sub, dist_comm, opposite_dist]
  ring

lemma outward_distance {q : Doubled V → ℝ} (hq : q ∈ polytope)
    (x : V) {t : ℝ} (ht : 0 ≤ t) :
    ‖mix q (profile (minus x)) t - q‖ =
      t * (commonRadius V - ‖q - profile (plus x)‖) := by
  have h : ‖q - profile (minus x)‖ = commonRadius V - ‖q - profile (plus x)‖ := by
    linarith [opposite_radii hq x]
  have hm := segment_distance q (profile (minus x)) t 0
  simpa only [mix_zero, sub_zero, abs_of_nonneg ht, norm_sub_rev (profile (minus x)) q, h]
    using hm

theorem radial_motion {q : Doubled V → ℝ} (hq : q ∈ polytope)
    (x : V) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (commonRadius V)) :
    ∃ z ∈ polytope, ‖z - profile (plus x)‖ = u ∧
      ‖z - q‖ = |u - ‖q - profile (plus x)‖| := by
  let ρ := ‖q - profile (plus x)‖
  have hρ : 0 ≤ ρ := norm_nonneg _
  by_cases h : u ≤ ρ
  · by_cases hz : ρ = 0
    · have hu0 : u = 0 := le_antisymm (hz ▸ h) hu.1
      refine ⟨q, hq, ?_, ?_⟩
      · exact hz.trans hu0.symm
      · simp only [sub_self, norm_zero]
        change 0 = |u - ρ|
        simp [hz, hu0]
    · have hpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hz)
      let t := (ρ - u) / ρ
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr h) hρ
      have ht1 : t ≤ 1 := (div_le_one hpos).2 (by linarith [hu.1])
      have htr : t * ρ = ρ - u := div_mul_cancel₀ _ hz
      refine ⟨mix q (profile (plus x)) t, mix_mem hq (profile_mem _) ⟨ht0, ht1⟩, ?_, ?_⟩
      · rw [inward_radius hq x ⟨ht0, ht1⟩]
        change (1 - t) * ρ = u
        nlinarith
      · rw [inward_distance q x ht0]
        change t * ρ = |u - ρ|
        rw [htr, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
  · have hlt : ρ < u := lt_of_not_ge h
    have hpos : 0 < commonRadius V - ρ := by linarith [hu.2]
    let t := (u - ρ) / (commonRadius V - ρ)
    have ht0 : 0 ≤ t := div_nonneg (sub_pos.mpr hlt).le hpos.le
    have ht1 : t ≤ 1 := (div_le_one hpos).2 (by linarith [hu.2])
    have htr : t * (commonRadius V - ρ) = u - ρ :=
      div_mul_cancel₀ _ (ne_of_gt hpos)
    refine ⟨mix q (profile (minus x)) t, mix_mem hq (profile_mem _) ⟨ht0, ht1⟩, ?_, ?_⟩
    · rw [outward_radius hq x ⟨ht0, ht1⟩]
      change ρ + t * (commonRadius V - ρ) = u
      rw [htr]
      ring
    · rw [outward_distance hq x ht0]
      change t * (commonRadius V - ρ) = |u - ρ|
      rw [htr, abs_of_nonneg (sub_nonneg.mpr hlt.le)]

theorem ball_intersects_shell {q : Doubled V → ℝ} (hq : q ∈ polytope) (x : V)
    {a b δ : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ commonRadius V)
    (hδ : 0 < δ) (hl : a - δ < ‖q - profile (plus x)‖)
    (hu : ‖q - profile (plus x)‖ < b + δ) :
    ∃ z ∈ polytope, ‖z - q‖ < δ ∧
      a < ‖z - profile (plus x)‖ ∧ ‖z - profile (plus x)‖ < b := by
  let ρ := ‖q - profile (plus x)‖
  have hgap : max a (ρ - δ) < min b (ρ + δ) := by
    apply max_lt
    · exact lt_min hab (by dsimp [ρ]; linarith)
    · exact lt_min (by dsimp [ρ]; linarith) (by linarith)
  obtain ⟨u, hlu, huu⟩ := exists_between hgap
  have hal : a < u := (le_max_left _ _).trans_lt hlu
  have hbu : u < b := huu.trans_le (min_le_left _ _)
  have hρl : ρ - δ < u := (le_max_right _ _).trans_lt hlu
  have hρu : u < ρ + δ := huu.trans_le (min_le_right _ _)
  obtain ⟨z, hz, hrad, hdist⟩ := radial_motion hq x ⟨ha.trans hal.le, hbu.le.trans hb⟩
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · rw [hdist]
    change |u - ρ| < δ
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · rwa [hrad]
  · rwa [hrad]

end RadialMotion

section PiecewiseAffine

def PiecewiseAffineOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ (N : ℕ) (pieces : Fin N → Set ℝ) (slopes intercepts : Fin N → ℝ),
    (∀ i, Convex ℝ (pieces i)) ∧ (∀ t ∈ s, ∃ i, t ∈ pieces i) ∧
    ∀ i t, t ∈ s → t ∈ pieces i → f t = slopes i * t + intercepts i

lemma PiecewiseAffineOn.mono {s t : Set ℝ} {f : ℝ → ℝ}
    (h : PiecewiseAffineOn s f) (ht : t ⊆ s) : PiecewiseAffineOn t f := by
  obtain ⟨N, pieces, slopes, intercepts, hc, hcover, heq⟩ := h
  exact ⟨N, pieces, slopes, intercepts, hc, fun u hu => hcover u (ht hu),
    fun i u hu hp => heq i u (ht hu) hp⟩

lemma PiecewiseAffineOn.congr {s : Set ℝ} {f g : ℝ → ℝ}
    (h : PiecewiseAffineOn s f) (hfg : ∀ t ∈ s, f t = g t) : PiecewiseAffineOn s g := by
  obtain ⟨N, pieces, slopes, intercepts, hc, hcover, heq⟩ := h
  exact ⟨N, pieces, slopes, intercepts, hc, hcover,
    fun i t ht hp => (hfg t ht).symm.trans (heq i t ht hp)⟩

lemma clamped_affine_piecewise {a b : ℝ} (hab : a ≤ b) (x y : ℝ) :
    PiecewiseAffineOn Set.univ (fun t : ℝ =>
      min b (max a ((1 - t) * x + t * y))) := by
  let f : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap x y
  refine ⟨3, ![f ⁻¹' Set.Iic a, f ⁻¹' Set.Icc a b, f ⁻¹' Set.Ici b],
    ![0, y - x, 0], ![a, x, b], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Convex.affine_preimage f (convex_Iic a)
    · exact Convex.affine_preimage f (convex_Icc a b)
    · exact Convex.affine_preimage f (convex_Ici b)
  · intro t _
    by_cases ha : f t ≤ a
    · exact ⟨0, ha⟩
    · by_cases hb : f t ≤ b
      · exact ⟨1, (lt_of_not_ge ha).le, hb⟩
      · exact ⟨2, (lt_of_not_ge hb).le⟩
  · intro i t _ hp
    fin_cases i
    · change f t ≤ a at hp
      have hp' : (1 - t) * x + t * y ≤ a := by
        simpa only [f, AffineMap.lineMap_apply_ring] using hp
      change min b (max a ((1 - t) * x + t * y)) = 0 * t + a
      rw [max_eq_left hp', min_eq_right hab, zero_mul, zero_add]
    · change a ≤ f t ∧ f t ≤ b at hp
      have hp' : a ≤ (1 - t) * x + t * y ∧ (1 - t) * x + t * y ≤ b := by
        simpa only [f, AffineMap.lineMap_apply_ring] using hp
      change min b (max a ((1 - t) * x + t * y)) = (y - x) * t + x
      rw [max_eq_right hp'.1, min_eq_right hp'.2]
      ring
    · change b ≤ f t at hp
      have hp' : b ≤ (1 - t) * x + t * y := by
        simpa only [f, AffineMap.lineMap_apply_ring] using hp
      change min b (max a ((1 - t) * x + t * y)) = 0 * t + b
      rw [max_eq_right (hab.trans hp'), min_eq_left hp', zero_mul, zero_add]

theorem clamped_radius_piecewise {V : Type*} [Fintype V] [PseudoMetricSpace V]
    {q r : V → ℝ} (hq : q ∈ polytope) (hr : r ∈ polytope) (x : V)
    {a b : ℝ} (hab : a ≤ b) :
    PiecewiseAffineOn (Set.Icc (0 : ℝ) 1)
      (fun t => min b (max a ‖mix q r t - profile x‖)) := by
  have h := (clamped_affine_piecewise hab ‖q - profile x‖ ‖r - profile x‖).mono
    (Set.subset_univ (Set.Icc (0 : ℝ) 1))
  apply h.congr
  intro t ht
  rw [radius_mix hq hr x ht]

end PiecewiseAffine

end AlgorithmicThinTrees.MetricProfiles

end 
end

end OAI
