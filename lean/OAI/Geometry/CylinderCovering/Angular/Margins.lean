import OAI.Geometry.CylinderCovering.Angular.MarginsDefinitions
import OAI.Geometry.CylinderCovering.Angular.Sampling

namespace OAI

open Set
noncomputable section
namespace CylinderCovering.Cubic

theorem profile_le_max_endpoints {a b q : ℝ} (ha : a ≤ q) (hb : q ≤ b) :
    profile q ≤ max (profile a) (profile b) := by
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
    dsimp [profile]
    nlinarith [sq_nonneg (a ^ 2 - q ^ 2), sq_nonneg q, sq_nonneg a,
      mul_nonneg (sub_nonneg.mpr h) (sq_nonneg q)]
  · apply le_trans _ (le_max_right _ _)
    dsimp [profile]
    nlinarith [sq_nonneg (b ^ 2 - q ^ 2), sq_nonneg q, sq_nonneg b,
      mul_nonneg (sub_nonneg.mpr h) (sq_nonneg q)]

theorem profile_bounds {q : ℝ} (hq : |q| ≤ 1) : 0 ≤ profile q ∧ profile q ≤ 1 := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [abs_le.mp hq, sq_abs q]
  constructor
  · unfold profile; positivity
  · unfold profile
    nlinarith [sq_nonneg q, mul_self_le_mul_self (sq_nonneg q) hq2]

theorem coeff_bounds {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 ≤ alpha a b ∧ alpha a b ≤ 1 ∧ |beta a b| ≤ 1 := by
  have hab : |a * b| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ha hb (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have ht : |a + b| ≤ 2 := (abs_add_le a b).trans (by linarith)
  dsimp [alpha, beta]
  constructor
  · linarith [(abs_le.mp hab).1]
  constructor
  · linarith [(abs_le.mp hab).2]
  · rw [abs_div]; norm_num
    linarith

theorem profile_nonneg (q : ℝ) : 0 ≤ profile q := by
  unfold profile
  positivity

theorem profileMax_nonneg (a b : ℝ) : 0 ≤ profileMax a b :=
  (profile_nonneg a).trans (le_max_left _ _)

theorem cap_pos {ε : ℝ} (he : 0 ≤ ε) (a b : ℝ) : 0 < cap ε a b := by
  have hm := profileMax_nonneg a b
  unfold cap
  positivity

theorem shared_left (a b : ℝ) : alpha a b - a * beta a b = (1 - a ^ 2) / 2 := by
  dsimp [alpha, beta]; ring

theorem shared_right (a b : ℝ) : alpha a b - b * beta a b = (1 - b ^ 2) / 2 := by
  dsimp [alpha, beta]; ring

theorem beta_error {a b q : ℝ} (ha : a ≤ q) (hb : q ≤ b) :
    |beta a b - q| ≤ (b - a) / 2 := by
  rw [abs_le]
  dsimp [beta]
  constructor <;> linarith

theorem alpha_error {a b q : ℝ} (ha : |a| ≤ 1) (hq : |q| ≤ 1)
    (haq : a ≤ q) (hqb : q ≤ b) :
    |alpha a b - (1 + q ^ 2) / 2| ≤ b - a := by
  have e : alpha a b - (1 + q ^ 2) / 2 = (a * (b - q) + q * (a - q)) / 2 := by
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

theorem step_pos {N : ℕ} (hN : 0 < N) : 0 < step N := by
  unfold step
  exact div_pos (by norm_num) (by exact_mod_cast hN)

@[simp] theorem node_zero (N : ℕ) : node N 0 = -1 := by simp [node]

@[simp] theorem node_last {N : ℕ} (hN : 0 < N) : node N N = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  dsimp [node, step]
  field_simp
  ring

theorem node_succ (N j : ℕ) : node N (j + 1) - node N j = step N := by
  simp [node]
  ring

theorem node_abs_le {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) : |node N j| ≤ 1 := by
  have h1 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have h2 : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hstep := step_pos hN
  have hn : (N : ℝ) * step N = 2 := by
    have := node_last hN
    dsimp [node] at this
    linarith only [this]
  rw [abs_le]
  dsimp [node]
  constructor
  · nlinarith only [mul_nonneg h1 hstep.le]
  · nlinarith only [mul_le_mul_of_nonneg_right h2 hstep.le, hn]

theorem angular_sector {N : ℕ} (hN : 0 < N) {r z ℓ : ℝ} (hz : |z| ≤ r) :
    ∃ j : ℕ, j < N ∧
      Sector (node N j) (node N (j + 1))
        (r - ℓ * beta (node N j) (node N (j + 1)))
        (z - ℓ * alpha (node N j) (node N (j + 1))) := by
  let f : ℕ → ℝ := fun i => node N i * r + ℓ * (1 - node N i ^ 2) / 2
  have hf0 : f 0 = -r := by simp [f]
  have hfN : f N = r := by simp [f, node_last hN]
  obtain ⟨j, hj, hlo, hhi⟩ := first_crossing hN f z
    (by rw [hf0]; exact (abs_le.mp hz).1)
    (by rw [hfN]; exact (abs_le.mp hz).2)
  let a := node N j
  let b := node N (j + 1)
  have he0 : f j = a * (r - ℓ * beta a b) + ℓ * alpha a b := by
    change a * r + ℓ * (1 - a ^ 2) / 2 = _
    dsimp [alpha, beta]; ring
  have he1 : f (j + 1) = b * (r - ℓ * beta a b) + ℓ * alpha a b := by
    change b * r + ℓ * (1 - b ^ 2) / 2 = _
    dsimp [alpha, beta]; ring
  rw [he0] at hlo
  rw [he1] at hhi
  have hlo' : a * (r - ℓ * beta a b) ≤ z - ℓ * alpha a b := by linarith only [hlo]
  have hhi' : z - ℓ * alpha a b ≤ b * (r - ℓ * beta a b) := by linarith only [hhi]
  have hdiff : 0 < b - a := by
    change 0 < node N (j + 1) - node N j
    rw [node_succ]
    exact step_pos hN
  refine ⟨j, hj, ?_, hlo', hhi'⟩
  have hmul : 0 ≤ (b - a) * (r - ℓ * beta a b) := by nlinarith only [hlo', hhi']
  exact nonneg_of_mul_nonneg_right hmul hdiff

theorem angle_in_interval {a b r z : ℝ} (hr : 0 < r) (hz : Sector a b r z) :
    a ≤ z / r ∧ z / r ≤ b := by
  exact ⟨(le_div_iff₀ hr).mpr hz.2.1, (div_le_iff₀ hr).mpr hz.2.2⟩

theorem abs_le_of_interval {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hqa : a ≤ q) (hqb : q ≤ b) : |q| ≤ 1 :=
  abs_le.mpr ⟨(abs_le.mp ha).1.trans hqa, hqb.trans (abs_le.mp hb).2⟩

theorem ceil_count_pos {ε : ℝ} (he : 0 < ε) : 0 < ⌈2 / ε ^ 2⌉₊ := by
  rw [Nat.ceil_pos]
  positivity

theorem ceil_step_le {ε : ℝ} (he : 0 < ε) : step ⌈2 / ε ^ 2⌉₊ ≤ ε ^ 2 := by
  have hn := ceil_count_pos he
  have hn' : (0 : ℝ) < ⌈2 / ε ^ 2⌉₊ := by exact_mod_cast hn
  unfold step
  rw [div_le_comm₀ hn' (sq_pos_of_pos he)]
  exact Nat.le_ceil _

theorem selected_cuts {ε Δ a b c e x y r s : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ 1 / 2) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ ε ^ 2)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (he : |e| ≤ 1)
    (hab : b - a = Δ) (hce : e - c = Δ) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hrs : r + s = 2 + ε * (beta c e * y - beta a b * x))
    (hqsec : Sector a b r (y - ε * x * alpha a b))
    (hpsec : Sector c e s (x + ε * y * alpha c e)) :
    r ≤ cap ε a b ∨ s ≤ cap ε c e := by
  by_contra! hbad
  have hr : 0 < r := lt_trans (cap_pos he0.le a b) hbad.1
  have hs : 0 < s := lt_trans (cap_pos he0.le c e) hbad.2
  let q := (y - ε * x * alpha a b) / r
  let p := (x + ε * y * alpha c e) / s
  have hqI : a ≤ q ∧ q ≤ b := angle_in_interval hr hqsec
  have hpI : c ≤ p ∧ p ≤ e := angle_in_interval hs hpsec
  have hq : |q| ≤ 1 := abs_le_of_interval ha hb hqI.1 hqI.2
  have hp : |p| ≤ 1 := abs_le_of_interval hc he hpI.1 hpI.2
  have h1 := coeff_bounds ha hb
  have h2 := coeff_bounds hc he
  have hβ : |beta a b - q| ≤ Δ := by
    have h := beta_error hqI.1 hqI.2
    rw [hab] at h
    linarith
  have hγ : |beta c e - p| ≤ Δ := by
    have h := beta_error hpI.1 hpI.2
    rw [hce] at h
    linarith
  have hea : alpha a b ≤ (1 + q ^ 2) / 2 + Δ := by
    have h := (abs_le.mp (alpha_error ha hq hqI.1 hqI.2)).2
    rw [hab] at h
    linarith
  have heb : alpha c e ≤ (1 + p ^ 2) / 2 + Δ := by
    have h := (abs_le.mp (alpha_error hc hp hpI.1 hpI.2)).2
    rw [hce] at h
    linarith
  have hM : (q ^ 2 + q ^ 4) / 2 ≤ profileMax a b := by
    have h := profile_le_max_endpoints hqI.1 hqI.2
    change profile q ≤ profileMax a b at h
    calc
      _ = profile q := by unfold profile; ring
      _ ≤ profileMax a b := h
  have hN : (p ^ 2 + p ^ 4) / 2 ≤ profileMax c e := by
    have h := profile_le_max_endpoints hpI.1 hpI.2
    change profile p ≤ profileMax c e at h
    calc
      _ = profile p := by unfold profile; ring
      _ ≤ profileMax c e := h
  have hy' : y = q * r + ε * alpha a b * x := by
    dsimp [q]
    field_simp
    ring
  have hx' : x = p * s - ε * alpha c e * y := by
    dsimp [p]
    field_simp
    ring
  have hcut := AngularSampling.noradial_failure he0 he1 hΔ0 hΔ1
    h1.1 h1.2.1 h2.1 h2.2.1 hβ hγ hq hp hx hy hy' hx' hrs hea heb hM hN
  exact hcut.elim (not_le.mpr hbad.1) (not_le.mpr hbad.2)

theorem finite_coordinate_cover {N : ℕ} {ε x y z : ℝ}
    (hN : 0 < N) (he0 : 0 < ε) (he1 : ε ≤ 1 / 2) (hmesh : step N ≤ ε ^ 2)
    (hx : |x| ≤ 1 - z) (hy : |y| ≤ 1 + z) :
    (∃ j : ℕ, j < N ∧ LowerHit N j ε x y z) ∨
    (∃ j : ℕ, j < N ∧ UpperHit N j ε x y z) := by
  obtain ⟨j, hj, hjs⟩ := angular_sector hN (ℓ := ε * x) hy
  obtain ⟨k, hk, hks⟩ := angular_sector hN (ℓ := -(ε * y)) hx
  have hks' : Sector (node N k) (node N (k + 1))
      (1 - z + ε * y * beta (node N k) (node N (k + 1)))
      (x + ε * y * alpha (node N k) (node N (k + 1))) := by
    simpa only [neg_mul, sub_neg_eq_add] using hks
  have hx2 : |x| ≤ 2 := by linarith only [hx, hy, abs_nonneg y]
  have hy2 : |y| ≤ 2 := by linarith only [hx, hy, abs_nonneg x]
  have hcuts := selected_cuts he0 he1 (step_pos hN).le hmesh
    (node_abs_le hN hj.le) (node_abs_le hN hj) (node_abs_le hN hk.le) (node_abs_le hN hk)
    (node_succ N j) (node_succ N k) hx2 hy2
    (show (1 + z - ε * x * beta (node N j) (node N (j + 1))) +
        (1 - z + ε * y * beta (node N k) (node N (k + 1))) =
      2 + ε * (beta (node N k) (node N (k + 1)) * y -
        beta (node N j) (node N (j + 1)) * x) by ring) hjs hks'
  exact hcuts.elim (fun h => Or.inl ⟨j, hj, hjs, h⟩) (fun h => Or.inr ⟨k, hk, hks', h⟩)

theorem finite_coordinate_cover_ceil {ε x y z : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ 1 / 2) (hx : |x| ≤ 1 - z) (hy : |y| ≤ 1 + z) :
    (∃ j : ℕ, j < ⌈2 / ε ^ 2⌉₊ ∧ LowerHit ⌈2 / ε ^ 2⌉₊ j ε x y z) ∨
    (∃ j : ℕ, j < ⌈2 / ε ^ 2⌉₊ ∧ UpperHit ⌈2 / ε ^ 2⌉₊ j ε x y z) :=
  finite_coordinate_cover (ceil_count_pos he0) he0 he1 (ceil_step_le he0) hx hy

end CylinderCovering.Cubic

end

end OAI
