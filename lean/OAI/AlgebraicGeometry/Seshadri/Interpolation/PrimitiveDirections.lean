import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.Moments

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
theorem exists_odd_integer_between (lo hi : ℝ) (hlen : 2 < hi - lo) :
    ∃ i : ℤ, Odd i ∧ lo < (i : ℝ) ∧ (i : ℝ) < hi := by
  let k : ℤ := ⌊(lo + 1) / 2⌋
  refine ⟨2 * k + 1, odd_two_mul_add_one k, ?_, ?_⟩
  · have h := Int.lt_floor_add_one ((lo + 1) / 2)
    change (lo + 1) / 2 < (k : ℝ) + 1 at h
    push_cast
    linarith
  · have h := Int.floor_le ((lo + 1) / 2)
    change (k : ℝ) ≤ (lo + 1) / 2 at h
    push_cast
    linarith

theorem primitive_direction_coordinates (d H T R : ℝ)
    (hd : 0 < d) (hH : 0 < H) (hT : 1 < T)
    (hR1 : 2 * (d * H) ≤ R) (hR2 : 8 * (1 + T) / d < R) :
    ∃ (t : ℝ) (i j : ℤ), T < t ∧ 0 < i ∧ 0 < j ∧ IsCoprime i j ∧
      (i : ℝ) / d + (j : ℝ) * (d * H * t / (1 + t)) = R ∧
      (j : ℝ) * (d * H / (1 + t)) < (i : ℝ) / d := by
  let W := d * H
  have hW : 0 < W := mul_pos hd hH
  have hR : 0 < R := lt_of_lt_of_le (by positivity : 0 < 2 * W) hR1
  have htwoW : 0 < 2 * W := by positivity
  have hx : 1 ≤ R / (2 * W) := (le_div_iff₀ htwoW).mpr (by simpa using hR1)
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  let j : ℤ := 2 ^ n
  have hj : 0 < j := pow_pos (by norm_num) _
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hjlo : (j : ℝ) * (2 * W) ≤ R := by
    apply (le_div_iff₀ htwoW).mp
    simpa [j] using hnlo
  have hjhi : R < (j : ℝ) * (4 * W) := by
    have h := (div_lt_iff₀ htwoW).mp hnhi
    rw [pow_succ] at h
    have hjcast : (j : ℝ) = (2 : ℝ) ^ n := by simp [j]
    rw [← hjcast] at h
    nlinarith only [h]
  let a₀ := W * T / (1 + T)
  have hTp : 0 < 1 + T := by linarith
  have ha₀ : a₀ * (1 + T) = W * T := div_mul_cancel₀ _ hTp.ne'
  have hgap : (W - a₀) * (1 + T) = W := by nlinarith only [ha₀]
  have hR2' : 8 * (1 + T) < d * R := by
    have h := (div_lt_iff₀ hd).mp hR2
    nlinarith only [h]
  have hintlen : 2 < d * (R - (j : ℝ) * a₀) - d * (R - (j : ℝ) * W) := by
    apply (mul_lt_mul_iff_left₀ hTp).mp
    have hprod := mul_lt_mul_of_pos_left hjhi hd
    have heq :
        (d * (R - (j : ℝ) * a₀) - d * (R - (j : ℝ) * W)) * (1 + T) =
          d * (j : ℝ) * W := by
      calc
        _ = d * (j : ℝ) * ((W - a₀) * (1 + T)) := by ring
        _ = _ := by rw [hgap]
    rw [heq]
    nlinarith only [hprod, hR2']
  obtain ⟨i, hiOdd, hilo, hihi⟩ := exists_odd_integer_between
    (d * (R - (j : ℝ) * W)) (d * (R - (j : ℝ) * a₀)) hintlen
  have hiR : 0 < (i : ℝ) := by
    have hprod : 0 < d * (R - (j : ℝ) * W) :=
      mul_pos hd (by nlinarith only [hjlo, hR])
    exact hprod.trans hilo
  have hi : 0 < i := by exact_mod_cast hiR
  have hprim : IsCoprime i j := (Int.isCoprime_two_right.mpr hiOdd).pow_right
  let a := (R - (i : ℝ) / d) / (j : ℝ)
  have ha : a * (j : ℝ) = R - (i : ℝ) / d := div_mul_cancel₀ _ hjR.ne'
  have hilo' : R - (j : ℝ) * W < (i : ℝ) / d :=
    (lt_div_iff₀ hd).mpr (by nlinarith only [hilo])
  have hihi' : (i : ℝ) / d < R - (j : ℝ) * a₀ :=
    (div_lt_iff₀ hd).mpr (by nlinarith only [hihi])
  have ha₀a : a₀ < a := by
    apply (mul_lt_mul_iff_left₀ hjR).mp
    nlinarith only [hihi', ha]
  have haW : a < W := by
    apply (mul_lt_mul_iff_left₀ hjR).mp
    nlinarith only [hilo', ha]
  have ha₀pos : 0 < a₀ := div_pos (mul_pos hW (by linarith)) hTp
  have hap : 0 < a := ha₀pos.trans ha₀a
  have hWa : 0 < W - a := sub_pos.mpr haW
  let t := a / (W - a)
  have ht : T < t := by
    apply (lt_div_iff₀ hWa).mpr
    nlinarith only [ha₀a, ha₀, hTp]
  have htp : 0 < 1 + t := by linarith
  have hta : W * t / (1 + t) = a := by
    dsimp [t]
    field_simp
    nlinarith only [haW, hW]
  have htb : W / (1 + t) = W - a := by
    have haeq := (div_eq_iff htp.ne').mp hta
    apply (div_eq_iff htp.ne').mpr
    nlinarith only [haeq]
  refine ⟨t, i, j, ht, hi, hj, hprim, ?_, ?_⟩
  · change (i : ℝ) / d + (j : ℝ) * (W * t / (1 + t)) = R
    rw [hta]
    nlinarith only [ha]
  · change (j : ℝ) * (W / (1 + t)) < (i : ℝ) / d
    rw [htb]
    nlinarith only [ha, hjlo, hR]

def compressedTriangle (d H t : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(-(d * H / (1 + t)), 0), (d * H * t / (1 + t), 0), (0, 1 / d)}

def directionProjection (i j : ℤ) (p : ℝ × ℝ) : ℝ :=
  (i : ℝ) * p.2 - (j : ℝ) * p.1

theorem compressedTriangle_projection_endpoints (d H t : ℝ) (i j : ℤ)
    (hd : 0 < d) (hH : 0 < H) (ht : 0 < t) (hi : 0 < i) (hj : 0 < j)
    (hsep : (j : ℝ) * (d * H / (1 + t)) < (i : ℝ) / d) :
    IsLeast (directionProjection i j '' compressedTriangle d H t)
      (-(j : ℝ) * (d * H * t / (1 + t))) ∧
    IsGreatest (directionProjection i j '' compressedTriangle d H t) ((i : ℝ) / d) := by
  have ha : 0 < d * H * t / (1 + t) := by positivity
  have hb : 0 < d * H / (1 + t) := by positivity
  have hi' : 0 < (i : ℝ) := by exact_mod_cast hi
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have hic : 0 < (i : ℝ) / d := div_pos hi' hd
  have hmin (p : ℝ × ℝ) (hp : p ∈ compressedTriangle d H t) :
      -(j : ℝ) * (d * H * t / (1 + t)) ≤ directionProjection i j p := by
    have hh := planeForm_nonneg_on_hull (-(j : ℝ)) (i : ℝ)
      ((j : ℝ) * (d * H * t / (1 + t)))
      {(-(d * H / (1 + t)), 0), (d * H * t / (1 + t), 0), (0, 1 / d)}
    have hy := hh (by
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;> dsimp [planeForm] <;>
        simp only [mul_zero, mul_one_div, zero_add, add_zero, neg_mul, mul_neg, neg_neg] <;>
        nlinarith only [mul_pos hj' ha, mul_pos hj' hb, hic]) p hp
    dsimp [planeForm, directionProjection] at *
    linarith
  have hmax (p : ℝ × ℝ) (hp : p ∈ compressedTriangle d H t) :
      directionProjection i j p ≤ (i : ℝ) / d := by
    have hh := planeForm_nonneg_on_hull (j : ℝ) (-(i : ℝ)) ((i : ℝ) / d)
      {(-(d * H / (1 + t)), 0), (d * H * t / (1 + t), 0), (0, 1 / d)}
    have hy := hh (by
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;> dsimp [planeForm]
      · nlinarith only [hsep]
      · simp only [mul_zero, add_zero]
        exact add_nonneg (mul_pos hj' ha).le hic.le
      · simp [div_eq_mul_inv]) p hp
    dsimp [planeForm, directionProjection] at *
    linarith
  have hB : (d * H * t / (1 + t), 0) ∈ compressedTriangle d H t :=
    subset_convexHull ℝ _ (by simp)
  have hC : (0, 1 / d) ∈ compressedTriangle d H t :=
    subset_convexHull ℝ _ (by simp)
  constructor
  · refine ⟨⟨_, hB, ?_⟩, ?_⟩
    · simp [directionProjection]
    · rintro y ⟨p, hp, rfl⟩
      exact hmin p hp
  · refine ⟨⟨_, hC, ?_⟩, ?_⟩
    · simp [directionProjection, div_eq_mul_inv]
    · rintro y ⟨p, hp, rfl⟩
      exact hmax p hp

theorem eventual_primitive_direction (d H T : ℝ)
    (hd : 0 < d) (hH : 0 < H) (hT : 1 < T) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ (t : ℝ) (i j : ℤ), T < t ∧ IsCoprime i j ∧
        sSup (directionProjection i j '' compressedTriangle d H t) -
          sInf (directionProjection i j '' compressedTriangle d H t) =
            Real.sqrt ((r : ℝ) * H) := by
  have hlim : Filter.Tendsto (fun r : ℕ => Real.sqrt ((r : ℝ) * H))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hH)
  have hev := (hlim.eventually (Filter.eventually_ge_atTop (2 * (d * H)))).and
    (hlim.eventually (Filter.eventually_gt_atTop (8 * (1 + T) / d)))
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max r₀ 1, by omega, ?_⟩
  intro r hr
  obtain ⟨hR1, hR2⟩ := hr₀ r (by omega)
  obtain ⟨t, i, j, ht, hi, hj, hprim, hlen, hsep⟩ :=
    primitive_direction_coordinates d H T (Real.sqrt ((r : ℝ) * H)) hd hH hT hR1 hR2
  obtain ⟨hmin, hmax⟩ := compressedTriangle_projection_endpoints d H t i j hd hH
    (by linarith) hi hj hsep
  refine ⟨t, i, j, ht, hprim, ?_⟩
  rw [hmin.csInf_eq, hmax.csSup_eq]
  nlinarith only [hlen]


end MaximalSeshadri.Interpolation
end

end OAI
