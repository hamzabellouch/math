import OAI.Geometry.TriangularCovering.Basic

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def η : ℝ := 1 / 1000

def alpha (a b : ℝ) : ℝ := (1 + a * b) / 4

def beta (a b : ℝ) : ℝ := (a + b) / 4

def d (q : ℝ) : ℝ := q ^ 2 * (1 + q ^ 2) / 16

/-- The maximum of d on an interval is attained at an endpoint. -/
theorem d_le_max_endpoints {a b q : ℝ} (ha : a ≤ q) (hb : q ≤ b) :
    d q ≤ max (d a) (d b) := by
  have hsq : q ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
    by_cases hq : 0 ≤ q
    · have hbb : 0 ≤ b := le_trans hq hb
      exact le_trans (sq_le_sq₀ hq hbb |>.mpr hb) (le_max_right _ _)
    · have hqa : a ≤ 0 := le_trans ha (le_of_not_ge hq)
      have hqa' : q ≤ 0 := le_of_not_ge hq
      have : q ^ 2 ≤ a ^ 2 := by nlinarith
      exact le_trans this (le_max_left _ _)
  rcases le_max_iff.mp hsq with h | h
  · apply le_trans _ (le_max_left _ _)
    dsimp [d]
    nlinarith [sq_nonneg (a ^ 2 - q ^ 2), sq_nonneg q, sq_nonneg a,
      mul_nonneg (sub_nonneg.mpr h) (sq_nonneg q)]
  · apply le_trans _ (le_max_right _ _)
    dsimp [d]
    nlinarith [sq_nonneg (b ^ 2 - q ^ 2), sq_nonneg q, sq_nonneg b,
      mul_nonneg (sub_nonneg.mpr h) (sq_nonneg q)]

def cutoffCoeff (a b : ℝ) : ℝ := η + max (d a) (d b)

theorem cutoffCoeff_eq_sSup {a b : ℝ} (hab : a ≤ b) :
    cutoffCoeff a b = η + sSup (d '' Icc a b) := by
  unfold cutoffCoeff
  congr 1
  apply le_antisymm
  · apply max_le
    · apply le_csSup
      · exact ⟨max (d a) (d b), by rintro z ⟨q, hq, rfl⟩; exact d_le_max_endpoints hq.1 hq.2⟩
      · exact ⟨a, ⟨le_rfl, hab⟩, rfl⟩
    · apply le_csSup
      · exact ⟨max (d a) (d b), by rintro z ⟨q, hq, rfl⟩; exact d_le_max_endpoints hq.1 hq.2⟩
      · exact ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  · apply csSup_le
    · exact ⟨d a, a, ⟨le_rfl, hab⟩, rfl⟩
    · rintro z ⟨q, hq, rfl⟩
      exact d_le_max_endpoints hq.1 hq.2

theorem d_bounds {q : ℝ} (hq : |q| ≤ 1) : 0 ≤ d q ∧ d q ≤ 1 / 8 := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [abs_le.mp hq, sq_abs q]
  constructor
  · unfold d; positivity
  · unfold d
    nlinarith [sq_nonneg q, mul_self_le_mul_self (sq_nonneg q) hq2]

theorem coeff_bounds {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 ≤ alpha a b ∧ alpha a b ≤ 1 / 2 ∧ |beta a b| ≤ 1 / 2 ∧
    η ≤ cutoffCoeff a b ∧ cutoffCoeff a b ≤ 1 / 8 + η := by
  have hab : |a * b| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ha hb (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have ht : |a + b| ≤ 2 := (abs_add_le a b).trans (by linarith)
  have da := d_bounds ha
  have db := d_bounds hb
  dsimp [alpha, beta, cutoffCoeff]
  constructor
  · linarith [(abs_le.mp hab).1]
  constructor
  · linarith [(abs_le.mp hab).2]
  constructor
  · rw [abs_div]; norm_num
    linarith
  constructor
  · have := le_max_left (d a) (d b); linarith
  · have := max_le da.2 db.2; linarith

theorem shared_left (a b : ℝ) : alpha a b - a * beta a b = (1 - a ^ 2) / 4 := by
  dsimp [alpha, beta]; ring

theorem shared_right (a b : ℝ) : alpha a b - b * beta a b = (1 - b ^ 2) / 4 := by
  dsimp [alpha, beta]; ring

theorem beta_error {a b q : ℝ} (ha : a ≤ q) (hb : q ≤ b) :
    |beta a b - q / 2| ≤ (b - a) / 4 := by
  rw [abs_le]
  dsimp [beta]
  constructor <;> linarith

theorem alpha_error {a b q : ℝ} (ha : |a| ≤ 1) (hq : |q| ≤ 1)
    (haq : a ≤ q) (hqb : q ≤ b) :
    |alpha a b - (1 + q ^ 2) / 4| ≤ (b - a) / 2 := by
  have e : alpha a b - (1 + q ^ 2) / 4 = (a * (b - q) + q * (a - q)) / 4 := by
    dsimp [alpha]; ring
  rw [e, abs_div]
  norm_num
  have h1 : |a * (b - q)| ≤ b - q := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hqb)]
    exact mul_le_of_le_one_left (sub_nonneg.mpr hqb) ha
  have h2 : |q * (a - q)| ≤ q - a := by
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr haq)]
    nlinarith [mul_le_of_le_one_left (sub_nonneg.mpr haq) hq]
  have h3 := abs_add_le (a * (b - q)) (q * (a - q))
  linarith

/-- First crossing in a finite sequence; no monotonicity is required. -/
theorem first_crossing {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) (z : ℝ)
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

/-- A uniform first-order estimate, used only after both cutoffs fail. -/
theorem rough_angle {ε x y q a r : ℝ} (he : 0 ≤ ε)
    (hx : |x| ≤ 1) (hq : |q| ≤ 1) (ha : |a| ≤ 1 / 2)
    (hr0 : 1 / 2 ≤ r) (hr1 : r ≤ 1 / 2 + ε / 2)
    (hy : y = r * q + ε * x * a) : |y - q / 2| ≤ ε := by
  have heq : y - q / 2 = (r - 1 / 2) * q + ε * x * a := by rw [hy]; ring
  have h1 : |(r - 1 / 2) * q| ≤ ε / 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ r - 1 / 2)]
    calc
      (r - 1 / 2) * |q| ≤ (r - 1 / 2) * 1 :=
        mul_le_mul_of_nonneg_left hq (by linarith)
      _ ≤ ε / 2 := by linarith
  have h2 : |ε * x * a| ≤ ε / 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg he]
    calc
      ε * |x| * |a| ≤ ε * 1 * (1 / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx he) ha (abs_nonneg _) (by positivity)
      _ = ε / 2 := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

theorem rough_square {ε x p : ℝ} (he : 0 ≤ ε) (hx : |x| ≤ 1) (hp : |p| ≤ 1)
    (h : |x - p / 2| ≤ ε) : |x ^ 2 - p ^ 2 / 4| ≤ 3 / 2 * ε := by
  have hsum : |x + p / 2| ≤ 3 / 2 := by
    have h' := abs_add_le x (p / 2)
    rw [abs_div] at h'
    norm_num at h'
    linarith
  calc
    |x ^ 2 - p ^ 2 / 4| = |x - p / 2| * |x + p / 2| := by
      rw [← abs_mul]; congr 1; ring
    _ ≤ ε * (3 / 2) := mul_le_mul h hsum (abs_nonneg _) he
    _ = 3 / 2 * ε := by ring

theorem cross_term_bound {ε Δ x y p q a b : ℝ}
    (he : 0 ≤ ε) (hΔ : 0 ≤ Δ) (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (hxp : |x ^ 2 - p ^ 2 / 4| ≤ 3 / 2 * ε)
    (hyq : |y ^ 2 - q ^ 2 / 4| ≤ 3 / 2 * ε)
    (ha : |a - (1 + q ^ 2) / 4| ≤ Δ / 2)
    (hb : |b - (1 + p ^ 2) / 4| ≤ Δ / 2) :
    x ^ 2 * a + y ^ 2 * b ≤ d p + d q + 3 / 2 * ε + Δ / 4 := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hp).1, (abs_le.mp hp).2]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hxa : x ^ 2 * a ≤ p ^ 2 / 4 * ((1 + q ^ 2) / 4) + 3 / 4 * ε + Δ / 8 := by
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp hxp).2 ha0
    have h2 := mul_le_mul_of_nonneg_left ha1 he
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp ha).2 (sq_nonneg p)
    have h4 := mul_le_mul_of_nonneg_right hp2 hΔ
    nlinarith
  have hyb : y ^ 2 * b ≤ q ^ 2 / 4 * ((1 + p ^ 2) / 4) + 3 / 4 * ε + Δ / 8 := by
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp hyq).2 hb0
    have h2 := mul_le_mul_of_nonneg_left hb1 he
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 (sq_nonneg q)
    have h4 := mul_le_mul_of_nonneg_right hq2 hΔ
    nlinarith
  dsimp [d]
  nlinarith [sq_nonneg (p ^ 2 - q ^ 2)]

theorem weighted_errors {ε Δ x y e f : ℝ} (he : 0 ≤ ε) (hΔ : 0 ≤ Δ)
    (hxy : |x| + |y| ≤ 1) (he' : |e| ≤ Δ / 4) (hf : |f| ≤ Δ / 4) :
    -ε * x * e + ε * y * f ≤ ε * Δ / 4 := by
  have h1 : -ε * x * e ≤ ε * |x| * (Δ / 4) := by
    calc
      -ε * x * e ≤ |-ε * x * e| := le_abs_self _
      _ = ε * |x| * |e| := by simp [abs_mul, abs_of_nonneg he]
      _ ≤ ε * |x| * (Δ / 4) := mul_le_mul_of_nonneg_left he' (by positivity)
  have h2 : ε * y * f ≤ ε * |y| * (Δ / 4) := by
    calc
      ε * y * f ≤ |ε * y * f| := le_abs_self _
      _ = ε * |y| * |f| := by simp [abs_mul, abs_of_nonneg he]
      _ ≤ ε * |y| * (Δ / 4) := mul_le_mul_of_nonneg_left hf (by positivity)
  have h3 := mul_le_mul_of_nonneg_right hxy (show 0 ≤ ε * Δ / 4 by positivity)
  nlinarith

/-- The exact cancellation which makes the secant construction work. -/
theorem radial_identity {ε x y q p a b β γ r s : ℝ}
    (hrs : r + s = 1 - ε * x * β + ε * y * γ)
    (hy : y = r * q + ε * x * a) (hx : x = s * p - ε * y * b) :
    (r - 1 / 2) * (1 - ε * x * q) + (s - 1 / 2) * (1 + ε * y * p) =
      ε ^ 2 * (x ^ 2 * a + y ^ 2 * b) - ε * x * (β - q / 2) + ε * y * (γ - p / 2) := by
  have hq : r * q = y - ε * x * a := by linarith
  have hp : s * p = x + ε * y * b := by linarith
  calc
    _ = r + s - 1 - ε * x * (r * q) + ε * x * q / 2 +
        ε * y * (s * p) - ε * y * p / 2 := by ring
    _ = _ := by rw [hrs, hq, hp]; ring

theorem radial_lower_est {ε M r f : ℝ} (heLt : ε < 1)
    (hM : 0 ≤ M) (hr : 1 / 2 + ε ^ 2 * M < r) (hf : 1 - ε ≤ f) :
    ε ^ 2 * M * (1 - ε) < (r - 1 / 2) * f := by
  calc
    _ ≤ ε ^ 2 * M * f := mul_le_mul_of_nonneg_left hf (by positivity)
    _ < _ := mul_lt_mul_of_pos_right (by linarith only [hr]) (by linarith only [heLt, hf])

theorem radial_failure {ε Δ x y q p a b β γ M N r s : ℝ}
    (he0 : 0 < ε) (heLt : ε < 1) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ ε ^ 2)
    (hxy : |x| + |y| ≤ 1) (hq : |q| ≤ 1) (hp : |p| ≤ 1)
    (hM0 : 0 ≤ M) (hN0 : 0 ≤ N)
    (heβ : |β - q / 2| ≤ Δ / 4) (heγ : |γ - p / 2| ≤ Δ / 4)
    (hrs : r + s = 1 - ε * x * β + ε * y * γ)
    (hy : y = r * q + ε * x * a) (hx : x = s * p - ε * y * b)
    (hr : 1 / 2 + ε ^ 2 * M < r) (hs : 1 / 2 + ε ^ 2 * N < s) :
    (M + N) * (1 - ε) < (x ^ 2 * a + y ^ 2 * b) + ε / 4 := by
  have he := he0.le
  have hx1 : |x| ≤ 1 := by linarith only [hxy, abs_nonneg y]
  have hy1 : |y| ≤ 1 := by linarith only [hxy, abs_nonneg x]
  have habsq : |x * q| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hx1 hq (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hbpsq : |y * p| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hy1 hp (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hf1 : 1 - ε ≤ 1 - ε * x * q := by
    nlinarith only [mul_le_mul_of_nonneg_left (abs_le.mp habsq).2 he]
  have hf2 : 1 - ε ≤ 1 + ε * y * p := by
    nlinarith only [mul_le_mul_of_nonneg_left (abs_le.mp hbpsq).1 he]
  have hstrict1 := radial_lower_est heLt hM0 hr hf1
  have hstrict2 := radial_lower_est heLt hN0 hs hf2
  have hid := radial_identity hrs hy hx
  have herr := weighted_errors he hΔ0 hxy heβ heγ
  have herr' : ε * Δ / 4 ≤ ε ^ 2 * (ε / 4) := by
    nlinarith only [mul_le_mul_of_nonneg_left hΔ1 he]
  have hscaled : ε ^ 2 * ((M + N) * (1 - ε)) <
      ε ^ 2 * ((x ^ 2 * a + y ^ 2 * b) + ε / 4) := by
    nlinarith only [hstrict1, hstrict2, hid, herr, herr']
  exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos he0)).mp hscaled

/-- Quantitative radial exclusion, with uniform constants independent of the mesh. -/
theorem radial_exclusion {ε Δ x y q p a b β γ M N r s : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ ε ^ 2)
    (hxy : |x| + |y| ≤ 1) (hq : |q| ≤ 1) (hp : |p| ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (hβ : |β| ≤ 1 / 2) (hγ : |γ| ≤ 1 / 2)
    (heβ : |β - q / 2| ≤ Δ / 4) (heγ : |γ - p / 2| ≤ Δ / 4)
    (hea : |a - (1 + q ^ 2) / 4| ≤ Δ / 2)
    (heb : |b - (1 + p ^ 2) / 4| ≤ Δ / 2)
    (hM : η + d q ≤ M) (hN : η + d p ≤ N)
    (hMN : M + N ≤ 1 / 4 + 2 * η)
    (hrs : r + s = 1 - ε * x * β + ε * y * γ)
    (hy : y = r * q + ε * x * a) (hx : x = s * p - ε * y * b) :
    r ≤ 1 / 2 + ε ^ 2 * M ∨ s ≤ 1 / 2 + ε ^ 2 * N := by
  by_contra! hbad
  have he : 0 ≤ ε := he0.le
  have hη : 0 < η := by norm_num [η]
  have heLt : ε < 1 := by unfold η at he1; linarith only [he1]
  have hx1 : |x| ≤ 1 := by linarith only [hxy, abs_nonneg y]
  have hy1 : |y| ≤ 1 := by linarith only [hxy, abs_nonneg x]
  have hM0 : 0 ≤ M := by linarith only [hM, hη, (d_bounds hq).1]
  have hN0 : 0 ≤ N := by linarith only [hN, hη, (d_bounds hp).1]
  have hr0 : 1 / 2 < r := by linarith only [hbad.1, mul_nonneg (sq_nonneg ε) hM0]
  have hs0 : 1 / 2 < s := by linarith only [hbad.2, mul_nonneg (sq_nonneg ε) hN0]
  have hsum : r + s ≤ 1 + ε / 2 := by
    have err := weighted_errors he (by norm_num : (0 : ℝ) ≤ 2) hxy
      (by norm_num; exact hβ) (by norm_num; exact hγ)
    rw [hrs]
    linarith only [err]
  have hr1 : r ≤ 1 / 2 + ε / 2 := by linarith only [hsum, hs0]
  have hs1 : s ≤ 1 / 2 + ε / 2 := by linarith only [hsum, hr0]
  have hqrough := rough_angle he hx1 hq (by rwa [abs_of_nonneg ha0]) hr0.le hr1 hy
  have hprough : |x - p / 2| ≤ ε := by
    apply rough_angle he hy1 hp (a := -b) (by simpa [abs_of_nonneg hb0] using hb1) hs0.le hs1
    linear_combination hx
  have hcross := cross_term_bound he hΔ0 hp hq ha0 ha1 hb0 hb1
    (rough_square he hx1 hp hprough) (rough_square he hy1 hq hqrough) hea heb
  have hfail := radial_failure he0 heLt hΔ0 hΔ1 hxy hq hp hM0 hN0 heβ heγ
    hrs hy hx hbad.1 hbad.2
  have hMN' : (M + N) * ε ≤ (1 / 4 + 2 * η) * ε :=
    mul_le_mul_of_nonneg_right hMN he
  have hgap : 0 < 2 * η - (2 + 2 * η) * ε - ε ^ 2 / 4 := by
    unfold η at he1 ⊢
    have he2 : ε ^ 2 ≤ (1 / 2000 : ℝ) ^ 2 := by nlinarith only [he1, he0]
    nlinarith only [he1, he2]
  nlinarith only [hfail, hcross, hM, hN, hMN', hΔ1, hgap]

def step (N : ℕ) : ℝ := 2 / N

def mesh (N i : ℕ) : ℝ := -1 + i * step N

theorem step_pos {N : ℕ} (hN : 0 < N) : 0 < step N := by
  unfold step
  exact div_pos (by norm_num) (by exact_mod_cast hN)

@[simp] theorem mesh_zero (N : ℕ) : mesh N 0 = -1 := by simp [mesh]

@[simp] theorem mesh_last {N : ℕ} (hN : 0 < N) : mesh N N = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  dsimp [mesh, step]
  field_simp
  ring

theorem mesh_succ (N j : ℕ) : mesh N (j + 1) - mesh N j = step N := by
  simp [mesh]
  ring

theorem mesh_abs_le {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) : |mesh N j| ≤ 1 := by
  have h1 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have h2 : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hstep := step_pos hN
  have hn : (N : ℝ) * step N = 2 := by
    have := mesh_last hN
    dsimp [mesh] at this
    linarith only [this]
  rw [abs_le]
  dsimp [mesh]
  constructor
  · nlinarith only [mul_nonneg h1 hstep.le]
  · nlinarith only [mul_le_mul_of_nonneg_right h2 hstep.le, hn]

/-- Both closed angular inequalities, including a nonnegative radial coordinate. -/
def Sector (a b r z : ℝ) : Prop := 0 ≤ r ∧ a * r ≤ z ∧ z ≤ b * r

theorem angular_sector {N : ℕ} (hN : 0 < N) {r z ℓ : ℝ} (hz : |z| ≤ r) :
    ∃ j : ℕ, j < N ∧
      Sector (mesh N j) (mesh N (j + 1))
        (r - ℓ * beta (mesh N j) (mesh N (j + 1)))
        (z - ℓ * alpha (mesh N j) (mesh N (j + 1))) := by
  let f : ℕ → ℝ := fun i => mesh N i * r + ℓ * (1 - mesh N i ^ 2) / 4
  have hf0 : f 0 = -r := by simp [f]
  have hfN : f N = r := by simp [f, mesh_last hN]
  obtain ⟨j, hj, hlo, hhi⟩ := first_crossing hN f z
    (by rw [hf0]; exact (abs_le.mp hz).1)
    (by rw [hfN]; exact (abs_le.mp hz).2)
  let a := mesh N j
  let b := mesh N (j + 1)
  have he0 : f j = a * (r - ℓ * beta a b) + ℓ * alpha a b := by
    change a * r + ℓ * (1 - a ^ 2) / 4 = _
    dsimp [alpha, beta]; ring
  have he1 : f (j + 1) = b * (r - ℓ * beta a b) + ℓ * alpha a b := by
    change b * r + ℓ * (1 - b ^ 2) / 4 = _
    dsimp [alpha, beta]; ring
  rw [he0] at hlo
  rw [he1] at hhi
  have hlo' : a * (r - ℓ * beta a b) ≤ z - ℓ * alpha a b := by linarith only [hlo]
  have hhi' : z - ℓ * alpha a b ≤ b * (r - ℓ * beta a b) := by linarith only [hhi]
  have hdiff : 0 < b - a := by
    change 0 < mesh N (j + 1) - mesh N j
    rw [mesh_succ]
    exact step_pos hN
  refine ⟨j, hj, ?_, hlo', hhi'⟩
  have hmul : 0 ≤ (b - a) * (r - ℓ * beta a b) := by nlinarith only [hlo', hhi']
  exact nonneg_of_mul_nonneg_right hmul hdiff

def cutoff (ε a b : ℝ) : ℝ := 1 / 2 + ε ^ 2 * cutoffCoeff a b

theorem cutoff_pos {ε a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : 0 < cutoff ε a b := by
  have h := (coeff_bounds ha hb).2.2.2.1
  have hM : 0 ≤ cutoffCoeff a b := by unfold η at h; linarith only [h]
  dsimp [cutoff]
  nlinarith only [mul_nonneg (sq_nonneg ε) hM]

theorem angle_in_interval {a b r z : ℝ} (hr : 0 < r) (hz : Sector a b r z) :
    a ≤ z / r ∧ z / r ≤ b := by
  exact ⟨(le_div_iff₀ hr).mpr hz.2.1, (div_le_iff₀ hr).mpr hz.2.2⟩

theorem abs_le_of_interval {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hqa : a ≤ q) (hqb : q ≤ b) : |q| ≤ 1 :=
  abs_le.mpr ⟨(abs_le.mp ha).1.trans hqa, hqb.trans (abs_le.mp hb).2⟩

theorem selected_cuts {ε Δ a b c e x y r s : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ ε ^ 2)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (he : |e| ≤ 1)
    (hab : b - a = Δ) (hce : e - c = Δ) (hxy : |x| + |y| ≤ 1)
    (hrs : r + s = 1 - ε * x * beta a b + ε * y * beta c e)
    (hqsec : Sector a b r (y - ε * x * alpha a b))
    (hpsec : Sector c e s (x + ε * y * alpha c e)) :
    r ≤ cutoff ε a b ∨ s ≤ cutoff ε c e := by
  by_contra! hbad
  have hr : 0 < r := lt_trans (cutoff_pos ha hb) hbad.1
  have hs : 0 < s := lt_trans (cutoff_pos hc he) hbad.2
  let q := (y - ε * x * alpha a b) / r
  let p := (x + ε * y * alpha c e) / s
  have hqI : a ≤ q ∧ q ≤ b := angle_in_interval hr hqsec
  have hpI : c ≤ p ∧ p ≤ e := angle_in_interval hs hpsec
  have hq : |q| ≤ 1 := abs_le_of_interval ha hb hqI.1 hqI.2
  have hp : |p| ≤ 1 := abs_le_of_interval hc he hpI.1 hpI.2
  have h1 := coeff_bounds ha hb
  have h2 := coeff_bounds hc he
  have hβ : |beta a b - q / 2| ≤ Δ / 4 := by simpa [hab] using beta_error hqI.1 hqI.2
  have hγ : |beta c e - p / 2| ≤ Δ / 4 := by simpa [hce] using beta_error hpI.1 hpI.2
  have hea : |alpha a b - (1 + q ^ 2) / 4| ≤ Δ / 2 := by
    simpa [hab] using alpha_error ha hq hqI.1 hqI.2
  have heb : |alpha c e - (1 + p ^ 2) / 4| ≤ Δ / 2 := by
    simpa [hce] using alpha_error hc hp hpI.1 hpI.2
  have hM : η + d q ≤ cutoffCoeff a b := by
    exact add_le_add_right (d_le_max_endpoints hqI.1 hqI.2) η
  have hN : η + d p ≤ cutoffCoeff c e := by
    exact add_le_add_right (d_le_max_endpoints hpI.1 hpI.2) η
  have hMN : cutoffCoeff a b + cutoffCoeff c e ≤ 1 / 4 + 2 * η := by
    linarith only [h1.2.2.2.2, h2.2.2.2.2]
  have hy : y = r * q + ε * x * alpha a b := by
    dsimp [q]
    field_simp
    ring
  have hx : x = s * p - ε * y * alpha c e := by
    dsimp [p]
    field_simp
    ring
  have hcut := radial_exclusion he0 he1 hΔ0 hΔ1 hxy hq hp
    h1.1 h1.2.1 h2.1 h2.2.1 h1.2.2.1 h2.2.2.1 hβ hγ hea heb hM hN hMN hrs hy hx
  exact hcut.elim (not_le.mpr hbad.1) (not_le.mpr hbad.2)

/-- Coordinate form of membership in the first intercept cylinder. -/
def LowerHit (N j : ℕ) (ε x y t : ℝ) : Prop :=
  Sector (mesh N j) (mesh N (j + 1))
    (t - ε * x * beta (mesh N j) (mesh N (j + 1)))
    (y - ε * x * alpha (mesh N j) (mesh N (j + 1))) ∧
  t - ε * x * beta (mesh N j) (mesh N (j + 1)) ≤ cutoff ε (mesh N j) (mesh N (j + 1))

/-- Coordinate form of membership in the second intercept cylinder. -/
def UpperHit (N j : ℕ) (ε x y t : ℝ) : Prop :=
  Sector (mesh N j) (mesh N (j + 1))
    (1 - t + ε * y * beta (mesh N j) (mesh N (j + 1)))
    (x + ε * y * alpha (mesh N j) (mesh N (j + 1))) ∧
  1 - t + ε * y * beta (mesh N j) (mesh N (j + 1)) ≤ cutoff ε (mesh N j) (mesh N (j + 1))

/-- Every boundary point is covered, not merely almost every point. -/
theorem finite_coordinate_cover {N : ℕ} {ε x y t : ℝ}
    (hN : 0 < N) (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hmesh : step N ≤ ε ^ 2)
    (hx : |x| ≤ 1 - t) (hy : |y| ≤ t) :
    (∃ j : ℕ, j < N ∧ LowerHit N j ε x y t) ∨
    (∃ j : ℕ, j < N ∧ UpperHit N j ε x y t) := by
  obtain ⟨j, hj, hjs⟩ := angular_sector hN (ℓ := ε * x) hy
  obtain ⟨k, hk, hks⟩ := angular_sector hN (ℓ := -(ε * y)) hx
  have hks' : Sector (mesh N k) (mesh N (k + 1))
      (1 - t + ε * y * beta (mesh N k) (mesh N (k + 1)))
      (x + ε * y * alpha (mesh N k) (mesh N (k + 1))) := by
    simpa only [neg_mul, sub_neg_eq_add] using hks
  have hcuts := selected_cuts he0 he1 (step_pos hN).le hmesh
    (mesh_abs_le hN hj.le) (mesh_abs_le hN hj) (mesh_abs_le hN hk.le) (mesh_abs_le hN hk)
    (mesh_succ N j) (mesh_succ N k) (by linarith only [hx, hy])
    (show (t - ε * x * beta (mesh N j) (mesh N (j + 1))) +
        (1 - t + ε * y * beta (mesh N k) (mesh N (k + 1))) =
      1 - ε * x * beta (mesh N j) (mesh N (j + 1)) +
        ε * y * beta (mesh N k) (mesh N (k + 1)) by ring) hjs hks'
  exact hcuts.elim (fun h => Or.inl ⟨j, hj, hjs, h⟩) (fun h => Or.inr ⟨k, hk, hks', h⟩)

theorem ceil_count_pos {ε : ℝ} (he : 0 < ε) : 0 < ⌈2 / ε ^ 2⌉₊ := by
  rw [Nat.ceil_pos]
  positivity

theorem ceil_step_le {ε : ℝ} (he : 0 < ε) : step ⌈2 / ε ^ 2⌉₊ ≤ ε ^ 2 := by
  have hn := ceil_count_pos he
  have hn' : (0 : ℝ) < ⌈2 / ε ^ 2⌉₊ := by exact_mod_cast hn
  unfold step
  rw [div_le_comm₀ hn' (sq_pos_of_pos he)]
  exact Nat.le_ceil _

/-- Coverage with the exact ceiling count, in intercept coordinates. -/
theorem finite_coordinate_cover_ceil {ε x y t : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hx : |x| ≤ 1 - t) (hy : |y| ≤ t) :
    (∃ j : ℕ, j < ⌈2 / ε ^ 2⌉₊ ∧ LowerHit ⌈2 / ε ^ 2⌉₊ j ε x y t) ∨
    (∃ j : ℕ, j < ⌈2 / ε ^ 2⌉₊ ∧ UpperHit ⌈2 / ε ^ 2⌉₊ j ε x y t) :=
  finite_coordinate_cover (ceil_count_pos he0) he0 he1 (ceil_step_le he0) hx hy

end TriangularCovering


namespace TriangularCovering

def speedSq (a b : ℝ) : ℝ := (alpha a b)^2 + 2*(beta a b)^2

def normalizedTerm (ε a b : ℝ) : ℝ :=
  (b-a) * (cutoff ε a b)^2 / Real.sqrt (1+ε^2*speedSq a b)

end TriangularCovering

end

end OAI
