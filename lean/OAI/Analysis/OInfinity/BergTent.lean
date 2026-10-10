import OAI.Analysis.OInfinity.BergShift

namespace OAI

/-! # Explicit finite Berg towers from unused Cuntz generators

The angular profile is a triangular tent. Two unused orthogonal isometries
supply its bottom partial isometry. This discharges the support and angular
hypotheses of the finite smoothing construction. It does not identify the
terminal corners belonging to two different Cuntz rows.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

/-- A tent of height `π / 2`, centered at `L`, with endpoints `0` and `2L`. -/
def bergTent (L x : ℝ) : ℝ := (Real.pi / (2 * L)) * max (L - |x - L|) 0

lemma bergTent_zero (L : ℝ) (hL : 0 ≤ L) : bergTent L 0 = 0 := by
  simp only [bergTent, zero_sub, abs_neg, abs_of_nonneg hL, sub_self, max_self, mul_zero]

lemma bergTent_peak (L : ℝ) (hL : 0 < L) : bergTent L L = Real.pi / 2 := by
  rw [bergTent, sub_self, abs_zero, sub_zero, max_eq_left hL.le]
  field_simp [hL.ne']

lemma bergTent_end (L : ℝ) (hL : 0 ≤ L) : bergTent L (2 * L) = 0 := by
  have he : 2 * L - L = L := by ring
  rw [bergTent, he, abs_of_nonneg hL, sub_self, max_self, mul_zero]

lemma bergTent_sub_le (L x y : ℝ) (hL : 0 < L) :
    |bergTent L x - bergTent L y| ≤ (Real.pi / (2 * L)) * |x - y| := by
  have hc : 0 ≤ Real.pi / (2 * L) := by positivity
  have hinner : |(L - |x - L|) - (L - |y - L|)| ≤ |x - y| := by
    calc
      _ = abs (abs (y - L) - abs (x - L)) := by congr 1; ring
      _ ≤ |(y - L) - (x - L)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |x - y| := by
        rw [show (y - L) - (x - L) = y - x by ring, abs_sub_comm]
  have hmax : |max (L - |x - L|) 0 - max (L - |y - L|) 0| ≤ |x - y| :=
    (abs_max_sub_max_le_abs _ _ _).trans hinner
  unfold bergTent
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left hmax hc

lemma bergTent_nat_step (K : ℕ) (hK : 0 < K) (k : ℕ) :
    |bergTent K (k + 1) - bergTent K k| ≤ Real.pi / (2 * (K : ℝ)) := by
  have h := bergTent_sub_le (K : ℝ) (k + 1) k (by exact_mod_cast hK)
  simpa only [add_sub_cancel_left, abs_one, mul_one] using h

variable {E : Type*} [CStarAlgebra E]

/-- Two unused ranges give a square-zero partial isometry. -/
def bergSpareCorner (r₀ r₁ : E) : E := r₁ * star r₀

lemma bergSpareCorner_source (r₀ r₁ : E) (hr₁ : star r₁ * r₁ = 1) :
    star (bergSpareCorner r₀ r₁) * bergSpareCorner r₀ r₁ = r₀ * star r₀ := by
  unfold bergSpareCorner
  rw [star_mul, star_star]
  calc
    _ = r₀ * (star r₁ * r₁) * star r₀ := by noncomm_ring
    _ = _ := by rw [hr₁, mul_one]

lemma bergSpareCorner_target (r₀ r₁ : E) (hr₀ : star r₀ * r₀ = 1) :
    bergSpareCorner r₀ r₁ * star (bergSpareCorner r₀ r₁) = r₁ * star r₁ := by
  unfold bergSpareCorner
  rw [star_mul, star_star]
  calc
    _ = r₁ * (star r₀ * r₀) * star r₁ := by noncomm_ring
    _ = _ := by rw [hr₀, mul_one]

lemma bergSpareCorner_partial (r₀ r₁ : E) (hr₀ : star r₀ * r₀ = 1)
    (hr₁ : star r₁ * r₁ = 1) :
    bergSpareCorner r₀ r₁ * star (bergSpareCorner r₀ r₁) *
      bergSpareCorner r₀ r₁ = bergSpareCorner r₀ r₁ := by
  rw [bergSpareCorner_target r₀ r₁ hr₀]
  unfold bergSpareCorner
  calc
    _ = r₁ * (star r₁ * r₁) * star r₀ := by noncomm_ring
    _ = _ := by rw [hr₁, mul_one]

lemma bergSpareCorner_square_zero (r₀ r₁ : E) (horth : star r₀ * r₁ = 0) :
    bergSpareCorner r₀ r₁ * bergSpareCorner r₀ r₁ = 0 := by
  unfold bergSpareCorner
  calc
    _ = r₁ * (star r₀ * r₁) * star r₀ := by noncomm_ring
    _ = 0 := by rw [horth, mul_zero, zero_mul]

section FiniteRow

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma bergSpareCorner_bottom_support (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (r₀ r₁ : E) (hr₀ : star r₀ * r₀ = 1) (hr₁ : star r₁ * r₁ = 1)
    (hsr₀ : ∀ i, star (s i) * r₀ = 0) (hsr₁ : ∀ i, star (s i) * r₁ = 0) :
    bergSupport (bergSpareCorner r₀ r₁) *
      bergTowerLayer (finiteCuntzDiagonalHom s hs) 0 =
      bergSupport (bergSpareCorner r₀ r₁) := by
  have hp : bergSupport (bergSpareCorner r₀ r₁) = r₀ * star r₀ + r₁ * star r₁ := by
    rw [bergSupport, bergSpareCorner_source r₀ r₁ hr₁, bergSpareCorner_target r₀ r₁ hr₀]
  have hr₀s (i : I) : star r₀ * s i = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star (hsr₀ i)
  have hr₁s (i : I) : star r₁ * s i = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star (hsr₁ i)
  have hzero : (r₀ * star r₀ + r₁ * star r₁) *
      finiteCuntzDiagonalHom s hs 1 = 0 := by
    change (r₀ * star r₀ + r₁ * star r₁) * (∑ i, s i * 1 * star (s i)) = 0
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [mul_one]
    calc
      _ = (r₀ * (star r₀ * s i) + r₁ * (star r₁ * s i)) * star (s i) := by
        noncomm_ring
      _ = 0 := by rw [hr₀s, hr₁s, mul_zero, mul_zero, zero_add, zero_mul]
  rw [hp, bergTowerLayer, bergTowerTail_zero, bergTowerTail_succ, bergTowerTail_zero,
    mul_sub, mul_one, hzero, sub_zero]

end FiniteRow

section InfiniteRow

variable [Nontrivial E]

lemma bergCuntzRow_norm_le_one (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (i : ℕ) : ‖s i‖ ≤ 1 := by
  have hii : star (s i) * s i = 1 := by simpa using hs i i
  have hn := congrArg norm hii
  rw [CStarRing.norm_star_mul_self, norm_one] at hn
  nlinarith only [hn, norm_nonneg (s i)]

/-- With an explicit tent profile, every angle and support hypothesis is
supplied by the infinite Cuntz row itself. The transported corner is the
`K`th iterate of the two unused generator ranges. -/
lemma exists_connected_cuntz_berg_tent (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n K : ℕ) (hK : 0 < K) :
    ∃ (u : unitary E) (b : E), Joined (1 : unitary E) u ∧
      (u : E) * (star b * b) = b ∧
      b = bergCornerIterHom
        (finiteCuntzDiagonalHom (fun i : Fin n => s i)
          (fun i j => by simpa only [Fin.ext_iff] using hs i j)) K
        (bergSpareCorner (s n) (s (n + 1))) ∧
      ∀ i < n, ‖(u : E) * s i - s i * (u : E)‖ ≤ Real.pi / (K : ℝ) := by
  have hsFin (i j : Fin n) : star (s i) * s j = if i = j then 1 else 0 := by
    simpa only [Fin.ext_iff] using hs i j
  let φ := finiteCuntzDiagonalHom (fun i : Fin n => s i) hsFin
  let a := bergSpareCorner (s n) (s (n + 1))
  let θ (k : ℕ) := bergTent K k
  have hr₀ : star (s n) * s n = 1 := by simpa using hs n n
  have hr₁ : star (s (n + 1)) * s (n + 1) = 1 := by
    simpa using hs (n + 1) (n + 1)
  have horth : star (s n) * s (n + 1) = 0 := by
    rw [hs, ite_eq_right (by omega)]
  have hbottom : bergSupport a * bergTowerLayer φ 0 = bergSupport a :=
    bergSpareCorner_bottom_support (fun i : Fin n => s i) hsFin _ _ hr₀ hr₁
      (fun i => by rw [hs, ite_eq_right (Nat.ne_of_lt i.isLt)])
      (fun i => by rw [hs, ite_eq_right (by omega)])
  have hKL : 0 < (K : ℝ) := by exact_mod_cast hK
  have hN : (2 * K - 1) + 1 = 2 * K := by omega
  have hpeak : θ K = Real.pi / 2 := bergTent_peak K hKL
  have hzero : θ 0 = 0 := by
    simpa only [θ, Nat.cast_zero] using bergTent_zero K hKL.le
  have hend : θ ((2 * K - 1) + 1) = 0 := by
    dsimp only [θ]
    rw [hN, Nat.cast_mul, Nat.cast_ofNat]
    exact bergTent_end K hKL.le
  obtain ⟨u, hu, hup, hcomm⟩ := exists_connected_berg_rotation
    (fun i : Fin n => s i) hsFin (fun i => bergCuntzRow_norm_le_one s hs i) a
    (bergSpareCorner_partial _ _ hr₀ hr₁) (bergSpareCorner_square_zero _ _ horth)
    hbottom θ (2 * K - 1) K (by omega) hpeak hzero hend
    (Real.pi / (2 * (K : ℝ))) (by positivity)
    (fun k _ => by
      simpa only [θ, Nat.cast_add, Nat.cast_one] using bergTent_nat_step K hK k)
  refine ⟨u, bergCornerIterHom φ K a, hu, hup, rfl, ?_⟩
  intro i hi
  have hc := hcomm ⟨i, hi⟩
  have he : 2 * (Real.pi / (2 * (K : ℝ))) = Real.pi / (K : ℝ) := by
    field_simp [hKL.ne']
  rwa [he] at hc

end InfiniteRow

end WeakPureInfiniteness

end

end OAI
