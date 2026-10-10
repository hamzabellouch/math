import Mathlib

namespace OAI

namespace CylinderCovering.GeneralCap

theorem quartic_bounds {q : ℝ} (hq : |q| ≤ 1) :
    0 ≤ (q ^ 2 + q ^ 4) / 16 ∧ (q ^ 2 + q ^ 4) / 16 ≤ 1 / 8 := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hq4 : q ^ 4 ≤ 1 := by nlinarith [sq_nonneg (q ^ 2 - 1)]
  constructor <;> nlinarith [sq_nonneg q, sq_nonneg (q ^ 2)]

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

theorem weighted_errors {ε E x y e f : ℝ} (he : 0 ≤ ε) (hE : 0 ≤ E)
    (hxy : |x| + |y| ≤ 1) (he' : |e| ≤ E) (hf : |f| ≤ E) :
    -ε * x * e + ε * y * f ≤ ε * E := by
  have h1 : -ε * x * e ≤ ε * |x| * E := by
    calc
      -ε * x * e ≤ |-ε * x * e| := le_abs_self _
      _ = ε * |x| * |e| := by simp [abs_mul, abs_of_nonneg he]
      _ ≤ ε * |x| * E := mul_le_mul_of_nonneg_left he' (by positivity)
  have h2 : ε * y * f ≤ ε * |y| * E := by
    calc
      ε * y * f ≤ |ε * y * f| := le_abs_self _
      _ = ε * |y| * |f| := by simp [abs_mul, abs_of_nonneg he]
      _ ≤ ε * |y| * E := mul_le_mul_of_nonneg_left hf (by positivity)
  have h3 := mul_le_mul_of_nonneg_right hxy (show 0 ≤ ε * E by positivity)
  nlinarith

theorem rough_angle {ε x y q a r : ℝ} (he : 0 ≤ ε)
    (hx : |x| ≤ 1) (hq : |q| ≤ 1) (ha : |a| ≤ 1)
    (hr0 : 1 / 2 ≤ r) (hr1 : r ≤ 1 / 2 + ε)
    (hy : y = r * q + ε * x * a) : |y - q / 2| ≤ 2 * ε := by
  have heq : y - q / 2 = (r - 1 / 2) * q + ε * x * a := by rw [hy]; ring
  have h1 : |(r - 1 / 2) * q| ≤ ε := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ r - 1 / 2)]
    calc
      (r - 1 / 2) * |q| ≤ (r - 1 / 2) * 1 :=
        mul_le_mul_of_nonneg_left hq (by linarith)
      _ ≤ ε := by linarith
  have h2 : |ε * x * a| ≤ ε := by
    rw [abs_mul, abs_mul, abs_of_nonneg he]
    calc
      ε * |x| * |a| ≤ ε * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx he) ha (abs_nonneg _) (by positivity)
      _ = ε := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

theorem rough_square {ε x p : ℝ} (he : 0 ≤ ε) (hx : |x| ≤ 1) (hp : |p| ≤ 1)
    (h : |x - p / 2| ≤ 2 * ε) : |x ^ 2 - p ^ 2 / 4| ≤ 3 * ε := by
  have hsum : |x + p / 2| ≤ 3 / 2 := by
    have h' := abs_add_le x (p / 2)
    rw [abs_div] at h'
    norm_num at h'
    linarith
  calc
    |x ^ 2 - p ^ 2 / 4| = |x - p / 2| * |x + p / 2| := by
      rw [← abs_mul]; congr 1; ring
    _ ≤ (2 * ε) * (3 / 2) := mul_le_mul h hsum (abs_nonneg _) (by positivity)
    _ = 3 * ε := by ring

theorem cross_term_bound {ε E x y p q a b : ℝ}
    (he : 0 ≤ ε) (hE : 0 ≤ E) (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hxp : |x ^ 2 - p ^ 2 / 4| ≤ 3 * ε)
    (hyq : |y ^ 2 - q ^ 2 / 4| ≤ 3 * ε)
    (ha : |a - (1 + q ^ 2) / 4| ≤ E)
    (hb : |b - (1 + p ^ 2) / 4| ≤ E) :
    x ^ 2 * a + y ^ 2 * b ≤
      (p ^ 2 + p ^ 4) / 16 + (q ^ 2 + q ^ 4) / 16 + 6 * ε + E / 2 := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp hp).1, (abs_le.mp hp).2]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hxa : x ^ 2 * a ≤ p ^ 2 / 4 * ((1 + q ^ 2) / 4) + 3 * ε + E / 4 := by
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp hxp).2 ha0
    have h2 := mul_le_mul_of_nonneg_left ha1 he
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp ha).2 (sq_nonneg p)
    have h4 := mul_le_mul_of_nonneg_right hp2 hE
    nlinarith
  have hyb : y ^ 2 * b ≤ q ^ 2 / 4 * ((1 + p ^ 2) / 4) + 3 * ε + E / 4 := by
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp hyq).2 hb0
    have h2 := mul_le_mul_of_nonneg_left hb1 he
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 (sq_nonneg q)
    have h4 := mul_le_mul_of_nonneg_right hq2 hE
    nlinarith
  nlinarith [sq_nonneg (p ^ 2 - q ^ 2)]

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

theorem radial_failure {ε K x y q p a b β γ M N r s : ℝ}
    (he0 : 0 < ε) (heLt : ε < 1) (hK : 0 ≤ K)
    (hxy : |x| + |y| ≤ 1) (hq : |q| ≤ 1) (hp : |p| ≤ 1)
    (hM0 : 0 ≤ M) (hN0 : 0 ≤ N)
    (heβ : |β - q / 2| ≤ K * ε ^ 2) (heγ : |γ - p / 2| ≤ K * ε ^ 2)
    (hrs : r + s = 1 - ε * x * β + ε * y * γ)
    (hy : y = r * q + ε * x * a) (hx : x = s * p - ε * y * b)
    (hr : 1 / 2 + ε ^ 2 * M < r) (hs : 1 / 2 + ε ^ 2 * N < s) :
    (M + N) * (1 - ε) < (x ^ 2 * a + y ^ 2 * b) + K * ε := by
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
  have herr := weighted_errors he (show 0 ≤ K * ε ^ 2 by positivity) hxy heβ heγ
  have hscaled : ε ^ 2 * ((M + N) * (1 - ε)) <
      ε ^ 2 * ((x ^ 2 * a + y ^ 2 * b) + K * ε) := by
    nlinarith only [hstrict1, hstrict2, hid, herr]
  exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos he0)).mp hscaled

theorem radial_exclusion {ε K η x y q p a b β γ r s R Q : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ 1 / 2) (hK : 0 ≤ K)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 480)
    (hsmall : (10 + 4 * K) * ε ≤ η)
    (hxy : |x| + |y| ≤ 1) (hq : |q| ≤ 1) (hp : |p| ≤ 1)
    (heβ : |β - q / 2| ≤ K * ε ^ 2) (heγ : |γ - p / 2| ≤ K * ε ^ 2)
    (hea : |a - (1 + q ^ 2) / 4| ≤ K * ε ^ 2)
    (heb : |b - (1 + p ^ 2) / 4| ≤ K * ε ^ 2)
    (hR : 1 / 2 + ε ^ 2 * ((q ^ 2 + q ^ 4) / 16 + η) - K * ε ^ 4 ≤ R)
    (hQ : 1 / 2 + ε ^ 2 * ((p ^ 2 + p ^ 4) / 16 + η) - K * ε ^ 4 ≤ Q)
    (hrs : r + s = 1 - ε * x * β + ε * y * γ)
    (hy : y = r * q + ε * x * a) (hx : x = s * p - ε * y * b) :
    r ≤ R ∨ s ≤ Q := by
  by_contra! hbad
  have he : 0 ≤ ε := he0.le
  have heLt : ε < 1 := by linarith only [he1]
  have hKE : K * ε ≤ η / 4 := by nlinarith only [hsmall, he0]
  have hKE0 : 0 ≤ K * ε := mul_nonneg hK he
  have hEη : K * ε ^ 2 ≤ η / 2 := by
    have h1 := mul_le_mul_of_nonneg_right hKE he
    have h2 := mul_le_mul_of_nonneg_left he1 hη0.le
    nlinarith only [h1, h2, hη0]
  have hE1 : K * ε ^ 2 ≤ 1 / 4 := by linarith only [hEη, hη1]
  have hEε : K * ε ^ 2 ≤ K * ε := by
    have h := mul_le_mul_of_nonneg_left he1 hKE0
    nlinarith only [h, hKE0]
  have hE0 : 0 ≤ K * ε ^ 2 := by positivity
  have hp2 : p ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp hp).1, (abs_le.mp hp).2]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have ha0 : 0 ≤ a := by nlinarith only [hE1, (abs_le.mp hea).1, sq_nonneg q]
  have hb0 : 0 ≤ b := by nlinarith only [hE1, (abs_le.mp heb).1, sq_nonneg p]
  have ha1 : a ≤ 1 := by nlinarith only [hE1, hq2, (abs_le.mp hea).2]
  have hb1 : b ≤ 1 := by nlinarith only [hE1, hp2, (abs_le.mp heb).2]
  have hβ : |β| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hE1, (abs_le.mp heβ).1, (abs_le.mp heβ).2,
      (abs_le.mp hq).1, (abs_le.mp hq).2]
  have hγ : |γ| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hE1, (abs_le.mp heγ).1, (abs_le.mp heγ).2,
      (abs_le.mp hp).1, (abs_le.mp hp).2]
  let M := (q ^ 2 + q ^ 4) / 16 + η - K * ε ^ 2
  let N := (p ^ 2 + p ^ 4) / 16 + η - K * ε ^ 2
  have hM0 : 0 ≤ M := by dsimp [M]; linarith only [hEη, hη0, (quartic_bounds hq).1]
  have hN0 : 0 ≤ N := by dsimp [N]; linarith only [hEη, hη0, (quartic_bounds hp).1]
  have hMN : M + N ≤ 3 := by
    dsimp [M, N]
    linarith only [(quartic_bounds hq).2, (quartic_bounds hp).2, hη1, hE0]
  have hr : 1 / 2 + ε ^ 2 * M < r := by
    dsimp [M]
    nlinarith only [hR, hbad.1]
  have hs : 1 / 2 + ε ^ 2 * N < s := by
    dsimp [N]
    nlinarith only [hQ, hbad.2]
  have hr0 : 1 / 2 < r := by linarith only [hr, mul_nonneg (sq_nonneg ε) hM0]
  have hs0 : 1 / 2 < s := by linarith only [hs, mul_nonneg (sq_nonneg ε) hN0]
  have hsum : r + s ≤ 1 + ε := by
    have err := weighted_errors he (by norm_num : (0 : ℝ) ≤ 1) hxy hβ hγ
    rw [hrs]
    linarith only [err]
  have hr1 : r ≤ 1 / 2 + ε := by linarith only [hsum, hs0]
  have hs1 : s ≤ 1 / 2 + ε := by linarith only [hsum, hr0]
  have hx1 : |x| ≤ 1 := by linarith only [hxy, abs_nonneg y]
  have hy1 : |y| ≤ 1 := by linarith only [hxy, abs_nonneg x]
  have hqrough := rough_angle he hx1 hq (by rwa [abs_of_nonneg ha0]) hr0.le hr1 hy
  have hprough : |x - p / 2| ≤ 2 * ε := by
    apply rough_angle he hy1 hp (a := -b) (by simpa [abs_of_nonneg hb0] using hb1) hs0.le hs1
    linear_combination hx
  have hcross := cross_term_bound he hE0 hp hq ha0 ha1 hb0 hb1
    (rough_square he hx1 hp hprough) (rough_square he hy1 hq hqrough) hea heb
  have hfail := radial_failure he0 heLt hK hxy hq hp hM0 hN0 heβ heγ hrs hy hx hr hs
  have hMNε := mul_le_mul_of_nonneg_right hMN he
  dsimp [M, N] at hfail hMNε
  nlinarith only [hfail, hcross, hMNε, hEε, hsmall, hη0, hKE0, he0]

theorem node_bounds {N : ℕ} (node : ℕ → ℝ)
    (h0 : node 0 = -1) (hN : node N = 1)
    (hstep : ∀ j < N, node j < node (j + 1)) :
    ∀ i ≤ N, |node i| ≤ 1 := by
  have hmono : MonotoneOn node (Set.Iic N) :=
    (strictMonoOn_Iic_of_lt_succ hstep).monotoneOn
  intro i hi
  have hl := hmono (show 0 ∈ Set.Iic N from Nat.zero_le N) hi (Nat.zero_le i)
  have hu := hmono hi (show N ∈ Set.Iic N by simp) hi
  rw [h0] at hl
  rw [hN] at hu
  exact abs_le.mpr ⟨hl, hu⟩

theorem angular_selection {N : ℕ} (hN : 0 < N)
    (node α β boundary : ℕ → ℝ)
    (hnode0 : node 0 = -1) (hnodeN : node N = 1)
    (hboundary0 : boundary 0 = 0) (hboundaryN : boundary N = 0)
    (hinc : ∀ j < N, node j < node (j + 1))
    (hleft : ∀ j < N, α j - node j * β j = boundary j)
    (hright : ∀ j < N, α j - node (j + 1) * β j = boundary (j + 1))
    {r z ℓ : ℝ} (hz : |z| ≤ r) :
    ∃ j : ℕ, j < N ∧ ∃ q : ℝ, q ∈ Set.Icc (node j) (node (j + 1)) ∧
      0 ≤ r - ℓ * β j ∧ z = (r - ℓ * β j) * q + ℓ * α j := by
  let f : ℕ → ℝ := fun i => node i * r + ℓ * boundary i
  have hf0 : f 0 = -r := by simp [f, hnode0, hboundary0]
  have hfN : f N = r := by simp [f, hnodeN, hboundaryN]
  obtain ⟨j, hj, hlo, hhi⟩ := first_crossing hN f z
    (by rw [hf0]; exact (abs_le.mp hz).1)
    (by rw [hfN]; exact (abs_le.mp hz).2)
  have he0 : f j = node j * (r - ℓ * β j) + ℓ * α j := by
    dsimp [f]
    rw [← hleft j hj]
    ring
  have he1 : f (j + 1) = node (j + 1) * (r - ℓ * β j) + ℓ * α j := by
    dsimp [f]
    rw [← hright j hj]
    ring
  rw [he0] at hlo
  rw [he1] at hhi
  have hlo' : node j * (r - ℓ * β j) ≤ z - ℓ * α j := by linarith only [hlo]
  have hhi' : z - ℓ * α j ≤ node (j + 1) * (r - ℓ * β j) := by linarith only [hhi]
  have hnonneg : 0 ≤ r - ℓ * β j := by
    have hmul : 0 ≤ (node (j + 1) - node j) * (r - ℓ * β j) := by
      nlinarith only [hlo', hhi']
    exact nonneg_of_mul_nonneg_right hmul (sub_pos.mpr (hinc j hj))
  by_cases hzero : r - ℓ * β j = 0
  · refine ⟨j, hj, node j, ⟨le_rfl, (hinc j hj).le⟩, hnonneg, ?_⟩
    rw [hzero]
    rw [hzero] at hlo' hhi'
    linarith only [hlo', hhi']
  · have hpos : 0 < r - ℓ * β j := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    refine ⟨j, hj, (z - ℓ * α j) / (r - ℓ * β j),
      ⟨(le_div_iff₀ hpos).mpr hlo', (div_le_iff₀ hpos).mpr hhi'⟩, hnonneg, ?_⟩
    field_simp
    ring

theorem coordinate_coverage {N : ℕ} (hN : 0 < N)
    (node α β boundary : ℕ → ℝ) (R : ℕ → ℝ → ℝ)
    (hnode0 : node 0 = -1) (hnodeN : node N = 1)
    (hnode : ∀ i ≤ N, |node i| ≤ 1)
    (hboundary0 : boundary 0 = 0) (hboundaryN : boundary N = 0)
    (hinc : ∀ j < N, node j < node (j + 1))
    (hleft : ∀ j < N, α j - node j * β j = boundary j)
    (hright : ∀ j < N, α j - node (j + 1) * β j = boundary (j + 1))
    {ε K η : ℝ} (he0 : 0 < ε) (he1 : ε ≤ 1 / 2) (hK : 0 ≤ K)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 480) (hsmall : (10 + 4 * K) * ε ≤ η)
    (hcoeff : ∀ j < N, ∀ q ∈ Set.Icc (node j) (node (j + 1)),
      |α j - (1 + q ^ 2) / 4| ≤ K * ε ^ 2 ∧ |β j - q / 2| ≤ K * ε ^ 2)
    (hcap : ∀ j < N, ∀ q ∈ Set.Icc (node j) (node (j + 1)),
      1 / 2 + ε ^ 2 * ((q ^ 2 + q ^ 4) / 16 + η) - K * ε ^ 4 ≤ R j q)
    {x y t : ℝ} (hx : |x| ≤ 1 - t) (hy : |y| ≤ t) :
    (∃ j : ℕ, j < N ∧ ∃ q : ℝ, q ∈ Set.Icc (node j) (node (j + 1)) ∧
      0 ≤ t - ε * x * β j ∧ t - ε * x * β j ≤ R j q ∧
      y = (t - ε * x * β j) * q + ε * x * α j) ∨
    (∃ j : ℕ, j < N ∧ ∃ p : ℝ, p ∈ Set.Icc (node j) (node (j + 1)) ∧
      0 ≤ 1 - t + ε * y * β j ∧ 1 - t + ε * y * β j ≤ R j p ∧
      x = (1 - t + ε * y * β j) * p - ε * y * α j) := by
  obtain ⟨j, hj, q, hqI, hr, hy'⟩ := angular_selection hN node α β boundary
    hnode0 hnodeN hboundary0 hboundaryN hinc hleft hright (ℓ := ε * x) hy
  obtain ⟨k, hk, p, hpI, hs, hx'⟩ := angular_selection hN node α β boundary
    hnode0 hnodeN hboundary0 hboundaryN hinc hleft hright (ℓ := -(ε * y)) hx
  have hs' : 0 ≤ 1 - t + ε * y * β k := by
    simpa only [neg_mul, sub_neg_eq_add] using hs
  have hx'' : x = (1 - t + ε * y * β k) * p - ε * y * α k := by
    linear_combination hx'
  have hq : |q| ≤ 1 := by
    apply abs_le.mpr
    exact ⟨(abs_le.mp (hnode j hj.le)).1.trans hqI.1,
      hqI.2.trans (abs_le.mp (hnode (j + 1) hj)).2⟩
  have hp : |p| ≤ 1 := by
    apply abs_le.mpr
    exact ⟨(abs_le.mp (hnode k hk.le)).1.trans hpI.1,
      hpI.2.trans (abs_le.mp (hnode (k + 1) hk)).2⟩
  have hcq := hcoeff j hj q hqI
  have hcp := hcoeff k hk p hpI
  have hcuts := radial_exclusion he0 he1 hK hη0 hη1 hsmall
    (show |x| + |y| ≤ 1 by linarith only [hx, hy]) hq hp hcq.2 hcp.2 hcq.1 hcp.1
    (hcap j hj q hqI) (hcap k hk p hpI)
    (show (t - ε * x * β j) + (1 - t + ε * y * β k) =
      1 - ε * x * β j + ε * y * β k by ring) hy' hx''
  exact hcuts.elim
    (fun h => Or.inl ⟨j, hj, q, hqI, hr, h, hy'⟩)
    (fun h => Or.inr ⟨k, hk, p, hpI, hs', h, hx''⟩)

theorem half_lt_cap {ε K η q R : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ 1 / 2) (_hK : 0 ≤ K) (hη : 0 < η)
    (hsmall : (10 + 4 * K) * ε ≤ η)
    (hR : 1 / 2 + ε ^ 2 * ((q ^ 2 + q ^ 4) / 16 + η) - K * ε ^ 4 ≤ R) :
    1 / 2 < R := by
  have hKE : K * ε ≤ η / 4 := by nlinarith only [hsmall, he0]
  have hEη : K * ε ^ 2 ≤ η / 2 := by
    have h1 := mul_le_mul_of_nonneg_right hKE he0.le
    have h2 := mul_le_mul_of_nonneg_left he1 hη.le
    nlinarith only [h1, h2, hη]
  have hd : 0 ≤ (q ^ 2 + q ^ 4) / 16 := by positivity
  have hm : 0 < (q ^ 2 + q ^ 4) / 16 + η - K * ε ^ 2 := by
    linarith only [hd, hEη, hη]
  have hprod := mul_pos (sq_pos_of_pos he0) hm
  nlinarith only [hR, hprod]

theorem exists_positive_threshold {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ε ≤ 1 / 2 ∧ (10 + 4 * K) * ε ≤ η := by
  have hd : 0 < 10 + 4 * K := by linarith only [hK]
  refine ⟨min (1 / 2) (η / (10 + 4 * K)), lt_min (by norm_num) (div_pos hη hd), ?_⟩
  intro ε _ hε
  refine ⟨hε.trans (min_le_left _ _), ?_⟩
  have hdiv := hε.trans (min_le_right _ _)
  have hmul := (le_div_iff₀ hd).mp hdiv
  nlinarith only [hmul]

end CylinderCovering.GeneralCap

end OAI
