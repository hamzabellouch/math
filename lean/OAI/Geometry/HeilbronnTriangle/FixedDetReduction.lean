import OAI.Geometry.HeilbronnTriangle.LatticeCoordinates

namespace OAI


noncomputable section

namespace Problem355.FixedDetReduction

open scoped BigOperators

def radius (X : ℝ) (ℓ : Fin 3 → ℝ) (j : Fin 3) : ℝ := 1000 * X / ℓ j

lemma log_radius_bound (X r : ℝ) (hX : 1 ≤ X) (hr : 1 ≤ r)
    (hrX : r ≤ 1000 * X) :
    Real.log (2 * r) ≤ 12 * Real.log (2 * X) := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog2 : Real.log 2 ≤ Real.log (2 * X) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hlogX : Real.log X ≤ Real.log (2 * X) :=
    Real.log_le_log hXp (by nlinarith)
  have hlog2000 : Real.log 2000 ≤ 11 * Real.log 2 := by
    have h := Real.log_le_log (show (0 : ℝ) < 2000 by norm_num)
      (show (2000 : ℝ) ≤ 2 ^ 11 by norm_num)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  calc
    Real.log (2 * r) ≤ Real.log (2000 * X) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log 2000 + Real.log X := Real.log_mul (by norm_num) hXp.ne'
    _ ≤ 11 * Real.log (2 * X) + Real.log (2 * X) :=
      add_le_add (hlog2000.trans (mul_le_mul_of_nonneg_left hlog2 (by norm_num))) hlogX
    _ = 12 * Real.log (2 * X) := by ring

lemma radius_antitone (X : ℝ) (ℓ : Fin 3 → ℝ) (hX : 0 ≤ X)
    (hℓ : ∀ j, 0 < ℓ j) (hmono : Monotone ℓ) : Antitone (radius X ℓ) := by
  intro i j hij
  exact div_le_div_of_nonneg_left (by positivity) (hℓ i) (hmono hij)

lemma one_le_radius (X : ℝ) (ℓ : Fin 3 → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (hℓX : ∀ j, ℓ j ≤ X) (j : Fin 3) : 1 ≤ radius X ℓ j := by
  apply (le_div_iff₀ (hℓ j)).mpr
  have hXp : 0 < X := lt_of_lt_of_le (hℓ j) (hℓX j)
  nlinarith [hℓX j]

lemma radius_product_bound (X I : ℝ) (ℓ : Fin 3 → ℝ)
    (hX : 0 ≤ X) (hI : 0 < I) (hℓ : ∀ j, 0 < ℓ j)
    (hIℓ : I ≤ ∏ j, ℓ j) :
    (∏ j, radius X ℓ j) ≤ (1000 * X) ^ 3 / I := by
  have hprod : 0 < ∏ j, ℓ j := Finset.prod_pos fun j hj => hℓ j
  calc
    (∏ j, radius X ℓ j) = (1000 * X) ^ 3 / (∏ j, ℓ j) := by
      simp [radius, Finset.prod_div_distrib]
    _ ≤ (1000 * X) ^ 3 / I :=
      div_le_div_of_nonneg_left (by positivity) hI hIℓ

theorem radius_count_factor_bound (X I : ℝ) (ℓ : Fin 3 → ℝ)
    (hX : 1 ≤ X) (hI : 0 < I) (hℓ1 : ∀ j, 1 ≤ ℓ j)
    (hℓX : ∀ j, ℓ j ≤ X) (hIℓ : I ≤ ∏ j, ℓ j) :
    (∏ j, radius X ℓ j) ^ 2 * Real.log (2 * radius X ℓ 0) ^ 2 ≤
      (1000 : ℝ) ^ 6 * 144 * (X ^ 6 / I ^ 2) * Real.log (2 * X) ^ 2 := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hℓ : ∀ j, 0 < ℓ j := fun j => lt_of_lt_of_le zero_lt_one (hℓ1 j)
  have hr : ∀ j, 1 ≤ radius X ℓ j := one_le_radius X ℓ hℓ hℓX
  have hrX : radius X ℓ 0 ≤ 1000 * X := by
    apply (div_le_iff₀ (hℓ 0)).mpr
    nlinarith [hℓ1 0]
  have hlog := log_radius_bound X (radius X ℓ 0) hX (hr 0) hrX
  have hlognonneg : 0 ≤ Real.log (2 * radius X ℓ 0) :=
    Real.log_nonneg (by nlinarith [hr 0])
  have hprodnonneg : 0 ≤ ∏ j, radius X ℓ j :=
    Finset.prod_nonneg fun j hj => le_trans zero_le_one (hr j)
  have hprod := radius_product_bound X I ℓ hXp.le hI hℓ hIℓ
  calc
    (∏ j, radius X ℓ j) ^ 2 * Real.log (2 * radius X ℓ 0) ^ 2 ≤
        ((1000 * X) ^ 3 / I) ^ 2 * (12 * Real.log (2 * X)) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ hprodnonneg hprod 2)
        (pow_le_pow_left₀ hlognonneg hlog 2) (sq_nonneg _) (sq_nonneg _)
    _ = (1000 : ℝ) ^ 6 * 144 * (X ^ 6 / I ^ 2) * Real.log (2 * X) ^ 2 := by
      ring

lemma coordinate_radius_le (X l : ℝ) (m : ℕ)
    (hX : 0 ≤ X) (hl : 0 < l) (hm : m ≤ 6) :
    Real.sqrt (Fintype.card (Fin 3)) *
      ((Nat.factorial (Fintype.card (Fin 3)) : ℝ) * 6 * ((m : ℝ) * X) / l) ≤
        1000 * X / l := by
  have hsqrt : Real.sqrt (3 : ℝ) ≤ 2 := by norm_num [Real.sqrt_le_iff]
  have hmR : (m : ℝ) ≤ 6 := by exact_mod_cast hm
  norm_num only [Fintype.card_fin, Nat.factorial, Nat.cast_ofNat]
  have hnum : Real.sqrt (3 : ℝ) * (36 * ((m : ℝ) * X)) ≤ 1000 * X := by
    calc
      Real.sqrt (3 : ℝ) * (36 * ((m : ℝ) * X)) ≤
          2 * (36 * (6 * X)) := by gcongr
      _ ≤ 1000 * X := by nlinarith
  calc
    Real.sqrt (3 : ℝ) * (36 * ((m : ℝ) * X) / l) =
        (Real.sqrt (3 : ℝ) * (36 * ((m : ℝ) * X))) / l := by ring
    _ ≤ 1000 * X / l := div_le_div_of_nonneg_right hnum hl.le

def AnisotropicEstimate (a : ℝ) : Prop :=
  ∀ (r : Fin 3 → ℝ) (u : ℤ) (T : Finset (Matrix (Fin 3) (Fin 3) ℤ)),
    Antitone r → 1 ≤ r 2 → u ≠ 0 →
    (∀ Q ∈ T, Q.det = u ∧ ∀ j,
      ‖(WithLp.toLp 2 (fun i => (Q i j : ℝ)) : EuclideanSpace ℝ (Fin 3))‖ ≤ r j) →
    (T.card : ℝ) ≤ a * (∏ j, r j) ^ 2 * Real.log (2 * r 0) ^ 2

theorem fixed_det_count_of_short_basis
    (a : ℝ) (ha : 0 ≤ a) (hanis : AnisotropicEstimate a)
    (V : Matrix (Fin 3) (Fin 3) ℝ) (m : ℕ) (hm : 0 < m) (hm6 : m ≤ 6)
    (ℓ : Fin 3 → ℝ) (X I : ℝ)
    (hV : V.det ≠ 0) (hℓ : ∀ i j, |V i j| ≤ ℓ i)
    (hℓ1 : ∀ j, 1 ≤ ℓ j) (hℓX : ∀ j, ℓ j ≤ X) (hmono : Monotone ℓ)
    (hX : 1 ≤ X) (hI : 0 < I) (hIℓ : I ≤ ∏ j, ℓ j)
    (hprod : (∏ j, ℓ j) ≤ 6 * |V.det|)
    (S : Finset (Matrix (Fin 3) (Fin 3) ℝ))
    (hspan : ∀ A ∈ S, ∀ i, m • A i ∈ Submodule.span ℤ (Set.range V))
    (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X)
    (t : ℝ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 / I ^ 2 := by
  classical
  by_cases hne : S.Nonempty
  · have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
    have hℓpos : ∀ j, 0 < ℓ j := fun j => lt_of_lt_of_le zero_lt_one (hℓ1 j)
    obtain ⟨u, hu, huvalue, T, hcard, hT⟩ :=
      LatticeCoordinates.exists_fixed_det_coordinate_family V m hm ℓ X 6 hV hℓ
        hℓpos hXp.le (by norm_num) hprod S hne hspan hbound t ht hdet
    have hcols : ∀ Q ∈ T, Q.det = u ∧ ∀ j,
        ‖(WithLp.toLp 2 (fun i => (Q i j : ℝ)) : EuclideanSpace ℝ (Fin 3))‖ ≤
          radius X ℓ j := by
      intro Q hQ
      refine ⟨(hT Q hQ).1, ?_⟩
      intro j
      exact ((hT Q hQ).2 j).trans (coordinate_radius_le X (ℓ j) m hXp.le (hℓpos j) hm6)
    have hcount := hanis (radius X ℓ) u T (radius_antitone X ℓ hXp.le hℓpos hmono)
      (one_le_radius X ℓ hℓpos hℓX 2) hu hcols
    have hfactor := radius_count_factor_bound X I ℓ hX hI hℓ1 hℓX hIℓ
    calc
      (S.card : ℝ) ≤ a * ((∏ j, radius X ℓ j) ^ 2 *
          Real.log (2 * radius X ℓ 0) ^ 2) := by
        simpa only [hcard, mul_assoc] using hcount
      _ ≤ a * (1000 ^ 6 * 144 * (X ^ 6 / I ^ 2) * Real.log (2 * X) ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor ha
      _ = (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 / I ^ 2 := by ring
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hS, Finset.card_empty, Nat.cast_zero]
    positivity

end Problem355.FixedDetReduction

end

end OAI
