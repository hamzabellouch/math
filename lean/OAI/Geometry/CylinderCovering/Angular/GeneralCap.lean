import Mathlib

namespace OAI

namespace AngularGeneralCap

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

theorem weighted_errors {τ D x y e f : ℝ} (ht : 0 ≤ τ) (hD : 0 ≤ D)
    (hxy : |x| + |y| ≤ 1) (he : |e| ≤ D) (hf : |f| ≤ D) :
    -τ * x * e + τ * y * f ≤ τ * D := by
  have h1 : -τ * x * e ≤ τ * |x| * D := by
    calc
      -τ * x * e ≤ |-τ * x * e| := le_abs_self _
      _ = τ * |x| * |e| := by simp [abs_mul, abs_of_nonneg ht]
      _ ≤ τ * |x| * D := mul_le_mul_of_nonneg_left he (by positivity)
  have h2 : τ * y * f ≤ τ * |y| * D := by
    calc
      τ * y * f ≤ |τ * y * f| := le_abs_self _
      _ = τ * |y| * |f| := by simp [abs_mul, abs_of_nonneg ht]
      _ ≤ τ * |y| * D := mul_le_mul_of_nonneg_left hf (by positivity)
  have h3 := mul_le_mul_of_nonneg_right hxy (mul_nonneg ht hD)
  nlinarith only [h1,h2,h3]

theorem rough_angle {τ x y q a r : ℝ} (ht : 0 ≤ τ)
    (hx : |x| ≤ 1) (hq : |q| ≤ 1) (ha : |a| ≤ 1)
    (hr0 : 1 / 2 ≤ r) (hr1 : r ≤ 1 / 2 + τ)
    (hy : y = r * q + τ * x * a) : |y - q / 2| ≤ 2 * τ := by
  have hid : y - q / 2 = (r - 1 / 2) * q + τ * x * a := by rw [hy]; ring
  have h1 : |(r - 1 / 2) * q| ≤ τ := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ r - 1 / 2)]
    calc
      (r - 1 / 2) * |q| ≤ (r - 1 / 2) * 1 :=
        mul_le_mul_of_nonneg_left hq (by linarith)
      _ ≤ τ := by linarith
  have h2 : |τ * x * a| ≤ τ := by
    rw [abs_mul,abs_mul,abs_of_nonneg ht]
    calc
      τ * |x| * |a| ≤ τ * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx ht) ha (abs_nonneg _) (by positivity)
      _ = τ := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith only [h1,h2])

theorem profile_bounds {q : ℝ} (hq : |q| ≤ 1) :
    0 ≤ (q^2+q^4)/16 ∧ (q^2+q^4)/16 ≤ 1/8 := by
  have h2 : q^2 ≤ 1 := by nlinarith [(abs_le.mp hq).1,(abs_le.mp hq).2]
  have h4 : q^4 ≤ 1 := by nlinarith [sq_nonneg (q^2-1),sq_nonneg q]
  constructor
  · positivity
  · linarith

theorem cross_term_bound {τ D x y p q a b : ℝ}
    (ht : 0 ≤ τ) (hD : 0 ≤ D) (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hxp : |x^2-p^2/4| ≤ 3*τ) (hyq : |y^2-q^2/4| ≤ 3*τ)
    (ha : |a-(1+q^2)/4| ≤ D) (hb : |b-(1+p^2)/4| ≤ D) :
    x^2*a+y^2*b ≤ (p^2+p^4)/16+(q^2+q^4)/16+6*τ+D/2 := by
  have hp2 : p^2 ≤ 1 := by nlinarith [(abs_le.mp hp).1,(abs_le.mp hp).2]
  have hq2 : q^2 ≤ 1 := by nlinarith [(abs_le.mp hq).1,(abs_le.mp hq).2]
  have hxa : x^2*a ≤ p^2/4*((1+q^2)/4)+3*τ+D/4 := by
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp hxp).2 ha0
    have h2 := mul_le_mul_of_nonneg_left ha1 ht
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp ha).2 (sq_nonneg p)
    have h4 := mul_le_mul_of_nonneg_right hp2 hD
    nlinarith only [h1,h2,h3,h4]
  have hyb : y^2*b ≤ q^2/4*((1+p^2)/4)+3*τ+D/4 := by
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp hyq).2 hb0
    have h2 := mul_le_mul_of_nonneg_left hb1 ht
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 (sq_nonneg q)
    have h4 := mul_le_mul_of_nonneg_right hq2 hD
    nlinarith only [h1,h2,h3,h4]
  nlinarith only [hxa,hyb,sq_nonneg (p^2-q^2)]

theorem radial_failure {τ C x y q p a b β γ M N r s : ℝ}
    (ht0 : 0 < τ) (ht1 : τ < 1) (hC : 0 ≤ C)
    (hxy : |x|+|y| ≤ 1) (hq : |q| ≤ 1) (hp : |p| ≤ 1)
    (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hβ : |β-q/2| ≤ C*τ^2) (hγ : |γ-p/2| ≤ C*τ^2)
    (hrs : r+s = 1-τ*x*β+τ*y*γ)
    (hy : y = r*q+τ*x*a) (hx : x = s*p-τ*y*b)
    (hr : 1/2+τ^2*M < r) (hs : 1/2+τ^2*N < s) :
    (M+N)*(1-τ) < x^2*a+y^2*b+C*τ := by
  have hx1 : |x| ≤ 1 := by linarith only [hxy,abs_nonneg y]
  have hy1 : |y| ≤ 1 := by linarith only [hxy,abs_nonneg x]
  have hxq : |x*q| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hx1 hq (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hyp : |y*p| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hy1 hp (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hf1 : 1-τ ≤ 1-τ*x*q := by
    nlinarith only [mul_le_mul_of_nonneg_left (abs_le.mp hxq).2 ht0.le]
  have hf2 : 1-τ ≤ 1+τ*y*p := by
    nlinarith only [mul_le_mul_of_nonneg_left (abs_le.mp hyp).1 ht0.le]
  have hl := radial_lower_est ht1 hM hr hf1
  have hu := radial_lower_est ht1 hN hs hf2
  have hi := radial_identity hrs hy hx
  have he := weighted_errors ht0.le (mul_nonneg hC (sq_nonneg τ)) hxy hβ hγ
  have hscaled : τ^2*((M+N)*(1-τ)) < τ^2*(x^2*a+y^2*b+C*τ) := by
    nlinarith only [hl,hu,hi,he]
  exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos ht0)).mp hscaled

theorem radial_exclusion {τ C η x y q p a b β γ r s R Q : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hC : 1 ≤ C)
    (ht0 : 0 < τ) (htsmall : τ ≤ η/(32*C))
    (hxy : |x|+|y| ≤ 1) (hq : |q| ≤ 1) (hp : |p| ≤ 1)
    (ha : |a-(1+q^2)/4| ≤ C*τ^2) (hb : |b-(1+p^2)/4| ≤ C*τ^2)
    (hβ : |β-q/2| ≤ C*τ^2) (hγ : |γ-p/2| ≤ C*τ^2)
    (hrs : r+s = 1-τ*x*β+τ*y*γ)
    (hy : y = r*q+τ*x*a) (hx : x = s*p-τ*y*b)
    (hR : 1/2+τ^2*((q^2+q^4)/16+η)-C*τ^4 ≤ R)
    (hQ : 1/2+τ^2*((p^2+p^4)/16+η)-C*τ^4 ≤ Q) :
    r ≤ R ∨ s ≤ Q := by
  have hC0 : 0 ≤ C := by linarith
  have hCpos : 0 < C := by linarith
  have hCt : C*τ ≤ η/32 := by
    have hh := (le_div_iff₀ (show 0 < 32*C by positivity)).mp htsmall
    nlinarith only [hh]
  have htC : τ ≤ C*τ := by nlinarith only [mul_le_mul_of_nonneg_right hC ht0.le]
  have ht1 : τ < 1 := by linarith only [hCt,htC,hη1]
  have ht1le : τ ≤ 1 := ht1.le
  have hCt2 : C*τ^2 ≤ C*τ := by
    have hh := mul_le_mul_of_nonneg_left ht1le (show 0 ≤ C*τ by positivity)
    nlinarith only [hh]
  have hCt2η : C*τ^2 ≤ η/2 := by linarith only [hCt2,hCt,hη0]
  have hCt2small : C*τ^2 ≤ 1/4 := by linarith only [hCt2,hCt,hη1]
  have hp2 : p^2 ≤ 1 := by nlinarith [(abs_le.mp hp).1,(abs_le.mp hp).2]
  have hq2 : q^2 ≤ 1 := by nlinarith [(abs_le.mp hq).1,(abs_le.mp hq).2]
  have ha0 : 0 ≤ a := by nlinarith only [(abs_le.mp ha).1,hCt2small,sq_nonneg q]
  have hb0 : 0 ≤ b := by nlinarith only [(abs_le.mp hb).1,hCt2small,sq_nonneg p]
  have ha1 : a ≤ 1 := by nlinarith only [(abs_le.mp ha).2,hCt2small,hq2]
  have hb1 : b ≤ 1 := by nlinarith only [(abs_le.mp hb).2,hCt2small,hp2]
  have hβ1 : |β| ≤ 1 := by
    have hh := abs_add_le (β-q/2) (q/2)
    have hqhalf : |q/2| ≤ 1/2 := by rw [abs_div]; norm_num; linarith
    rw [sub_add_cancel] at hh
    linarith only [hh,hqhalf,hβ,hCt2small]
  have hγ1 : |γ| ≤ 1 := by
    have hh := abs_add_le (γ-p/2) (p/2)
    have hphalf : |p/2| ≤ 1/2 := by rw [abs_div]; norm_num; linarith
    rw [sub_add_cancel] at hh
    linarith only [hh,hphalf,hγ,hCt2small]
  let M := (q^2+q^4)/16+η/2
  let N := (p^2+p^4)/16+η/2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hR' : 1/2+τ^2*M ≤ R := by
    have hh := mul_le_mul_of_nonneg_left hCt2η (sq_nonneg τ)
    dsimp [M]
    nlinarith only [hR,hh]
  have hQ' : 1/2+τ^2*N ≤ Q := by
    have hh := mul_le_mul_of_nonneg_left hCt2η (sq_nonneg τ)
    dsimp [N]
    nlinarith only [hQ,hh]
  by_contra! hbad
  have hr : 1/2+τ^2*M < r := hR'.trans_lt hbad.1
  have hs : 1/2+τ^2*N < s := hQ'.trans_lt hbad.2
  have hr0 : 1/2 < r := by nlinarith only [hr,mul_nonneg (sq_nonneg τ) hM]
  have hs0 : 1/2 < s := by nlinarith only [hs,mul_nonneg (sq_nonneg τ) hN]
  have hsum : r+s ≤ 1+τ := by
    have hh := weighted_errors ht0.le (by norm_num : (0:ℝ) ≤ 1) hxy hβ1 hγ1
    rw [hrs]
    linarith only [hh]
  have hr1 : r ≤ 1/2+τ := by linarith only [hsum,hs0]
  have hs1 : s ≤ 1/2+τ := by linarith only [hsum,hr0]
  have hx1 : |x| ≤ 1 := by linarith only [hxy,abs_nonneg y]
  have hy1 : |y| ≤ 1 := by linarith only [hxy,abs_nonneg x]
  have hyq := rough_angle ht0.le hx1 hq (by rwa [abs_of_nonneg ha0]) hr0.le hr1 hy
  have hxp : |x-p/2| ≤ 2*τ := by
    apply rough_angle ht0.le hy1 hp (a := -b) (by simpa [abs_of_nonneg hb0] using hb1) hs0.le hs1
    linear_combination hx
  have hx2 : |x^2-p^2/4| ≤ 3*τ := by
    have hh := rough_square (show 0 ≤ 2*τ by positivity) hx1 hp hxp
    nlinarith only [hh]
  have hy2 : |y^2-q^2/4| ≤ 3*τ := by
    have hh := rough_square (show 0 ≤ 2*τ by positivity) hy1 hq hyq
    nlinarith only [hh]
  have hcross := cross_term_bound ht0.le (show 0 ≤ C*τ^2 by positivity) hp hq
    ha0 ha1 hb0 hb1 hx2 hy2 ha hb
  have hfail := radial_failure ht0 ht1 hC0 hxy hq hp hM hN hβ hγ hrs hy hx hr hs
  have hdp := profile_bounds hp
  have hdq := profile_bounds hq
  have hMN : M+N ≤ 1/4+η := by dsimp [M,N]; linarith only [hdp.2,hdq.2]
  have hMNτ := mul_le_mul_of_nonneg_right hMN ht0.le
  have hητ := mul_le_mul_of_nonneg_right hη1 ht0.le
  dsimp [M,N] at hfail hMNτ
  nlinarith only [hfail,hcross,hMNτ,hητ,hCt2,hCt,htC,hη0]

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

theorem compatible_sector {n : ℕ} (hn : 0 < n) (node L α β : ℕ → ℝ)
    (hnode0 : node 0 = -1) (hnoden : node n = 1)
    (hL0 : L 0 = 0) (hLn : L n = 0)
    (hstep : ∀ j < n, node j < node (j+1))
    (hleft : ∀ j < n, α j-node j*β j = L j)
    (hright : ∀ j < n, α j-node (j+1)*β j = L (j+1))
    {t y ℓ : ℝ} (hy : |y| ≤ t) :
    ∃ j < n, 0 ≤ t-ℓ*β j ∧
      node j*(t-ℓ*β j) ≤ y-ℓ*α j ∧
      y-ℓ*α j ≤ node (j+1)*(t-ℓ*β j) := by
  let f := fun i => node i*t+ℓ*L i
  have h0 : f 0 ≤ y := by
    dsimp [f]; rw [hnode0,hL0]; nlinarith only [(abs_le.mp hy).1]
  have hN : y ≤ f n := by
    dsimp [f]; rw [hnoden,hLn]; nlinarith only [(abs_le.mp hy).2]
  obtain ⟨j,hj,hj0,hj1⟩ := first_crossing hn f y h0 hN
  have hl : node j*(t-ℓ*β j) ≤ y-ℓ*α j := by
    dsimp [f] at hj0
    rw [← hleft j hj] at hj0
    nlinarith only [hj0]
  have hr : y-ℓ*α j ≤ node (j+1)*(t-ℓ*β j) := by
    dsimp [f] at hj1
    rw [← hright j hj] at hj1
    nlinarith only [hj1]
  have hrad : 0 ≤ t-ℓ*β j := by
    have hp : 0 < node (j+1)-node j := sub_pos.mpr (hstep j hj)
    have hh : 0 ≤ (node (j+1)-node j)*(t-ℓ*β j) := by nlinarith only [hl,hr]
    exact nonneg_of_mul_nonneg_right hh hp
  exact ⟨j,hj,hrad,hl,hr⟩

theorem sector_parameter {l u r z : ℝ} (hlu : l ≤ u) (hr : 0 ≤ r)
    (hl : l*r ≤ z) (hu : z ≤ u*r) :
    ∃ q, l ≤ q ∧ q ≤ u ∧ z = r*q := by
  by_cases hz : r = 0
  · refine ⟨l,le_rfl,hlu,?_⟩
    simp only [hz,mul_zero] at hl hu
    simp only [hz,zero_mul]
    linarith only [hl,hu]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    refine ⟨z/r,(le_div_iff₀ hrp).mpr hl,(div_le_iff₀ hrp).mpr hu,?_⟩
    field_simp

theorem finite_coordinate_cover {n : ℕ} (hn : 0 < n)
    (node L α β : ℕ → ℝ) (cap : ℕ → ℝ → ℝ)
    (hnode0 : node 0 = -1) (hnoden : node n = 1)
    (hL0 : L 0 = 0) (hLn : L n = 0)
    (hstep : ∀ j < n, node j < node (j+1))
    (hbound : ∀ j ≤ n, |node j| ≤ 1)
    (hleft : ∀ j < n, α j-node j*β j = L j)
    (hright : ∀ j < n, α j-node (j+1)*β j = L (j+1))
    {τ C η x y t : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hC : 1 ≤ C)
    (ht0 : 0 < τ) (htsmall : τ ≤ η/(32*C))
    (hα : ∀ j < n, ∀ q, node j ≤ q → q ≤ node (j+1) →
      |α j-(1+q^2)/4| ≤ C*τ^2)
    (hβ : ∀ j < n, ∀ q, node j ≤ q → q ≤ node (j+1) →
      |β j-q/2| ≤ C*τ^2)
    (hcap : ∀ j < n, ∀ q, node j ≤ q → q ≤ node (j+1) →
      1/2+τ^2*((q^2+q^4)/16+η)-C*τ^4 ≤ cap j q)
    (hx : |x| ≤ 1-t) (hy : |y| ≤ t) :
    (∃ j < n, ∃ q, node j ≤ q ∧ q ≤ node (j+1) ∧
      ∃ S, 0 ≤ S ∧ S ≤ cap j q ∧ t = S+τ*x*β j ∧ y = S*q+τ*x*α j) ∨
    (∃ j < n, ∃ q, node j ≤ q ∧ q ≤ node (j+1) ∧
      ∃ T, 0 ≤ T ∧ T ≤ cap j q ∧ 1-t = T-τ*y*β j ∧ x = T*q-τ*y*α j) := by
  obtain ⟨j,hj,hS,hlj,hrj⟩ := compatible_sector hn node L α β
    hnode0 hnoden hL0 hLn hstep hleft hright (ℓ := τ*x) hy
  obtain ⟨k,hk,hT,hlk,hrk⟩ := compatible_sector hn node L α β
    hnode0 hnoden hL0 hLn hstep hleft hright (ℓ := -(τ*y)) hx
  simp only [neg_mul,sub_neg_eq_add] at hT hlk hrk
  obtain ⟨q,hql,hqr,hqeq⟩ := sector_parameter (hstep j hj).le hS hlj hrj
  obtain ⟨p,hpl,hpr,hpeq⟩ := sector_parameter (hstep k hk).le hT hlk hrk
  have hq : |q| ≤ 1 := abs_le.mpr
    ⟨(abs_le.mp (hbound j hj.le)).1.trans hql,
      hqr.trans (abs_le.mp (hbound (j+1) (by omega))).2⟩
  have hp : |p| ≤ 1 := abs_le.mpr
    ⟨(abs_le.mp (hbound k hk.le)).1.trans hpl,
      hpr.trans (abs_le.mp (hbound (k+1) (by omega))).2⟩
  have hyeq : y = (t-τ*x*β j)*q+τ*x*α j := by linarith only [hqeq]
  have hxeq : x = (1-t+τ*y*β k)*p-τ*y*α k := by linarith only [hpeq]
  have hchoice := radial_exclusion hη0 hη1 hC ht0 htsmall
    (show |x|+|y| ≤ 1 by linarith only [hx,hy]) hq hp
    (hα j hj q hql hqr) (hα k hk p hpl hpr)
    (hβ j hj q hql hqr) (hβ k hk p hpl hpr)
    (show (t-τ*x*β j)+(1-t+τ*y*β k) = 1-τ*x*β j+τ*y*β k by ring)
    hyeq hxeq (hcap j hj q hql hqr) (hcap k hk p hpl hpr)
  rcases hchoice with hjcap | hkcap
  · exact Or.inl ⟨j,hj,q,hql,hqr,t-τ*x*β j,hS,hjcap,by ring,hyeq⟩
  · exact Or.inr ⟨k,hk,p,hpl,hpr,1-t+τ*y*β k,hT,hkcap,by ring,hxeq⟩

end AngularGeneralCap

end OAI
