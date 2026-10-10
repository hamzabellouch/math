import OAI.Geometry.CylinderCovering.Cartesian.CapsDefinitions

namespace OAI

namespace CylinderCovering.CartesianCaps

open Set

lemma D_nonneg (a : ℝ) : 0 ≤ D a := by
  unfold D
  positivity

lemma D_le (a : ℝ) (ha : |a| ≤ 1) : D a ≤ 5 / 4 := by
  have h2 : a ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
  have h4 : a ^ 4 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg a)]
  unfold D
  linarith

lemma D_sub_factor (a b : ℝ) :
    D a - D b = (a - b) * ((a + b) * (1 / 4 + a ^ 2 + b ^ 2)) := by
  unfold D
  ring

lemma D_lipschitz (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |D a - D b| ≤ (9 / 2) * |a - b| := by
  have h2a : a ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
  have h2b : b ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one b).2 hb
  have hab : |a + b| ≤ 2 := (abs_add_le a b).trans (by linarith)
  have hfac : |(a + b) * (1 / 4 + a ^ 2 + b ^ 2)| ≤ 9 / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / 4 : ℝ) + a ^ 2 + b ^ 2)]
    calc
      |a + b| * (1 / 4 + a ^ 2 + b ^ 2) ≤ 2 * (1 / 4 + a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_right hab (by positivity)
      _ ≤ 9 / 2 := by linarith
  rw [D_sub_factor, abs_mul]
  nlinarith [abs_nonneg (a-b)]

lemma abs_mul_le_one (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a * b| ≤ 1 := by
  rw [abs_mul]
  calc
    |a| * |b| ≤ 1 * 1 := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

lemma D_ray_lipschitz (q s t : ℝ) (hq : |q| ≤ 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |D (q * s) - D (q * t)| ≤ (9 / 2) * |s - t| := by
  have hs' : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have h := D_lipschitz (q*s) (q*t) (abs_mul_le_one q s hq hs')
    (abs_mul_le_one q t hq ht')
  have hmul : |q*s-q*t| ≤ |s-t| := by
    rw [← mul_sub, abs_mul]
    nlinarith [abs_nonneg (s-t)]
  linarith

lemma small_square (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4)) : τ ^ 2 ≤ 1/16 := by
  nlinarith [hτ.1, hτ.2]

lemma residual_strictMono (τ η q : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hq : |q| ≤ 1) : StrictMonoOn (residual τ η q) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hl := D_ray_lipschitz q t s hq ht hs
  rw [abs_of_pos (sub_pos.mpr hst)] at hl
  have hd : D (q*t) - D (q*s) ≤ (9/2)*(t-s) := (le_abs_self _).trans hl
  have hsq := small_square τ hτ
  have hmult := mul_le_mul_of_nonneg_left hd (sq_nonneg τ)
  have hb := mul_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr hst.le)
  unfold residual
  nlinarith

lemma root_exists (τ η q : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hq : |q| ≤ 1) :
    ∃ s : ℝ, s ∈ Icc (1/2 : ℝ) (3/4) ∧ residual τ η q s = 0 := by
  have hc : ContinuousOn (residual τ η q) (Icc (1/2 : ℝ) (3/4)) := by
    unfold residual D
    fun_prop
  have hleft : residual τ η q (1/2) ≤ 0 := by
    have hp : 0 ≤ τ ^ 2 * (D (q * (1/2)) + η) :=
      mul_nonneg (sq_nonneg τ) (by linarith [D_nonneg (q*(1/2)), hη.1])
    unfold residual
    linarith
  have habs : |q * (3/4)| ≤ 1 := abs_mul_le_one q (3/4) hq (by norm_num)
  have hd := D_le (q*(3/4)) habs
  have hsq := small_square τ hτ
  have hright : 0 ≤ residual τ η q (3/4) := by
    have h := mul_le_mul_of_nonneg_left (show D (q*(3/4))+η ≤ 9/4 by linarith [hη.2]) (sq_nonneg τ)
    unfold residual
    nlinarith
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc (by norm_num : (1/2 : ℝ) ≤ 3/4) hc ⟨hleft, hright⟩
  exact ⟨s, hs, he⟩

lemma cap_spec (τ η q : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hq : |q| ≤ 1) :
    cap τ η q ∈ Icc (1/2 : ℝ) (3/4) ∧ residual τ η q (cap τ η q) = 0 := by
  have h := root_exists τ η q hτ hη hq
  unfold cap
  rw [dite_eq_left h]
  exact Classical.choose_spec h

lemma cap_equation (τ η q : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hq : |q| ≤ 1) :
    cap τ η q = 1/2 + τ^2 * (D (q * cap τ η q) + η) := by
  have h := (cap_spec τ η q hτ hη hq).2
  unfold residual at h
  linarith

lemma cap_mem_unit (τ η q : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hq : |q| ≤ 1) :
    cap τ η q ∈ Icc (0 : ℝ) 1 := by
  have h := (cap_spec τ η q hτ hη hq).1
  constructor <;> linarith [h.1, h.2]

lemma cap_unique (τ η q s : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hq : |q| ≤ 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (he : residual τ η q s = 0) :
    s = cap τ η q := by
  apply (residual_strictMono τ η q hτ hq).injOn hs (cap_mem_unit τ η q hτ hη hq)
  rw [he, (cap_spec τ η q hτ hη hq).2]

lemma residual_nonpos_iff (τ η q s : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hq : |q| ≤ 1)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    residual τ η q s ≤ 0 ↔ s ≤ cap τ η q := by
  have hc := cap_mem_unit τ η q hτ hη hq
  have he := (cap_spec τ η q hτ hη hq).2
  have hm := residual_strictMono τ η q hτ hq
  constructor
  · intro h
    by_contra hn
    have hlt := hm hc hs (lt_of_not_ge hn)
    rw [he] at hlt
    linarith
  · intro h
    have hle := hm.monotoneOn hs hc h
    rwa [he] at hle

lemma aperture_eq_Icc (τ η b q : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Icc (3/4 : ℝ) 1)
    (hq : |q| ≤ 1) : aperture τ η b q = Icc 0 (cap τ η q) := by
  ext s
  constructor
  · rintro ⟨hs0, hsb, hs⟩
    refine ⟨hs0, (residual_nonpos_iff τ η q s hτ hη hq ⟨hs0, hsb.trans hb.2⟩).1 ?_⟩
    unfold residual
    linarith
  · rintro ⟨hs0, hsR⟩
    have hR := (cap_spec τ η q hτ hη hq).1
    have hsb : s ≤ b := by linarith [hR.2, hb.1]
    refine ⟨hs0, hsb, ?_⟩
    have h := (residual_nonpos_iff τ η q s hτ hη hq ⟨hs0, hsb.trans hb.2⟩).2 hsR
    unfold residual at h
    linarith

lemma cap_lipschitz (τ η : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (p q : ℝ) (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    |cap τ η p - cap τ η q| ≤ |p - q| := by
  have hRp := cap_mem_unit τ η p hτ hη hp
  have hRq := cap_mem_unit τ η q hτ hη hq
  have hRap : |cap τ η p| ≤ 1 := by rw [abs_of_nonneg hRp.1]; exact hRp.2
  have hRaq : |cap τ η q| ≤ 1 := by rw [abs_of_nonneg hRq.1]; exact hRq.2
  have hd := D_lipschitz (p * cap τ η p) (q * cap τ η q)
    (abs_mul_le_one p _ hp hRap) (abs_mul_le_one q _ hq hRaq)
  have hm : |p * cap τ η p - q * cap τ η q| ≤
      |cap τ η p - cap τ η q| + |p-q| := by
    calc
      |p * cap τ η p - q * cap τ η q| =
          |p * (cap τ η p - cap τ η q) + (p-q) * cap τ η q| := by congr 1; ring
      _ ≤ |p * (cap τ η p - cap τ η q)| + |(p-q) * cap τ η q| := abs_add_le _ _
      _ ≤ |cap τ η p - cap τ η q| + |p-q| := by
        rw [abs_mul, abs_mul]
        have h1 := mul_le_mul_of_nonneg_right hp (abs_nonneg (cap τ η p - cap τ η q))
        have h2 := mul_le_mul_of_nonneg_left hRaq (abs_nonneg (p-q))
        nlinarith
  have he : cap τ η p - cap τ η q =
      τ^2 * (D (p * cap τ η p) - D (q * cap τ η q)) := by
    linarith [cap_equation τ η p hτ hη hp, cap_equation τ η q hτ hη hq]
  have ha : |cap τ η p - cap τ η q| =
      τ^2 * |D (p * cap τ η p) - D (q * cap τ η q)| := by
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg τ)]
  have hu : |cap τ η p - cap τ η q| ≤
      τ^2 * ((9/2) * (|cap τ η p - cap τ η q| + |p-q|)) := by
    rw [ha]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg τ)
    linarith
  have ht := mul_le_mul_of_nonneg_right (small_square τ hτ)
    (show 0 ≤ (9/2 : ℝ) * (|cap τ η p - cap τ η q| + |p-q|) by positivity)
  nlinarith [abs_nonneg (cap τ η p - cap τ η q), abs_nonneg (p-q)]

lemma cap_continuousOn (τ η : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) : ContinuousOn (cap τ η) (Icc (-1 : ℝ) 1) := by
  have h : LipschitzOnWith 1 (cap τ η) (Icc (-1 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    simpa [Real.dist_eq] using cap_lipschitz τ η hτ hη p q
      (abs_le.mpr hp) (abs_le.mpr hq)
  exact h.continuousOn

lemma D_half (q : ℝ) : D (q * (1/2)) = d q := by
  unfold D d
  ring

lemma cap_quadratic_bound (τ η q : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hq : |q| ≤ 1) :
    |cap τ η q - 1/2| ≤ (9/4) * τ^2 := by
  have hc := (cap_spec τ η q hτ hη hq).1
  have hcu := cap_mem_unit τ η q hτ hη hq
  have hca : |cap τ η q| ≤ 1 := by rw [abs_of_nonneg hcu.1]; exact hcu.2
  have hd := D_le (q * cap τ η q) (abs_mul_le_one q _ hq hca)
  rw [abs_of_nonneg (by linarith [hc.1] : 0 ≤ cap τ η q - 1/2)]
  have hm := mul_le_mul_of_nonneg_left (show D (q * cap τ η q) + η ≤ 9/4 by linarith [hη.2]) (sq_nonneg τ)
  linarith [cap_equation τ η q hτ hη hq]

lemma cap_fourth_order (τ η q : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) (hq : |q| ≤ 1) :
    |cap τ η q - (1/2 + τ^2 * (d q + η))| ≤ 12 * τ^4 := by
  have hc := cap_mem_unit τ η q hτ hη hq
  have hl := D_ray_lipschitz q (cap τ η q) (1/2) hq hc (by norm_num)
  have hb := cap_quadratic_bound τ η q hτ hη hq
  have he : cap τ η q - (1/2 + τ^2 * (d q + η)) =
      τ^2 * (D (q * cap τ η q) - D (q * (1/2))) := by
    rw [D_half]
    linarith [cap_equation τ η q hτ hη hq]
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg τ)]
  calc
    τ^2 * |D (q * cap τ η q) - D (q * (1/2))| ≤ τ^2 * ((9/2) * ((9/4) * τ^2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg τ)
      linarith
    _ ≤ 12 * τ^4 := by nlinarith [sq_nonneg (τ^2)]

theorem cap_properties (τ η : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (1/4))
    (hη : η ∈ Ioc (0 : ℝ) 1) :
    ContinuousOn (cap τ η) (Icc (-1 : ℝ) 1) ∧
      ∀ q ∈ Icc (-1 : ℝ) 1,
        cap τ η q ∈ Icc (1/2 : ℝ) (3/4) ∧
        residual τ η q (cap τ η q) = 0 ∧
        (∀ s ∈ Icc (0 : ℝ) 1, residual τ η q s = 0 → s = cap τ η q) ∧
        |cap τ η q - (1/2 + τ^2 * (d q + η))| ≤ 12 * τ^4 ∧
        ∀ b ∈ Icc (3/4 : ℝ) 1, aperture τ η b q = Icc 0 (cap τ η q) := by
  refine ⟨cap_continuousOn τ η hτ hη, ?_⟩
  intro q hq
  have haq : |q| ≤ 1 := abs_le.mpr hq
  refine ⟨(cap_spec τ η q hτ hη haq).1, (cap_spec τ η q hτ hη haq).2, ?_,
    cap_fourth_order τ η q hτ hη haq, ?_⟩
  · intro s hs he
    exact cap_unique τ η q s hτ hη haq hs he
  · intro b hb
    exact aperture_eq_Icc τ η b q hτ hη hb haq

end CylinderCovering.CartesianCaps

end OAI
