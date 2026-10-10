import Mathlib

namespace OAI


namespace Problem355.SuccessiveBox

open MeasureTheory Set
open scoped BigOperators

theorem box_volume_le {ι : Type*} [Fintype ι]
    (L : AddSubgroup (ι → ℝ)) [Countable L] (F : Set (ι → ℝ))
    (hF : IsAddFundamentalDomain L F volume) (w : ι → ℝ)
    (hempty : ∀ x : L, (∀ i, |(x : ι → ℝ) i| < w i) → x = 0) :
    (∏ i, ENNReal.ofReal (2 * w i)) ≤ volume F * 2 ^ Fintype.card ι := by
  let S : Set (ι → ℝ) := Set.pi Set.univ (fun i => Set.Ioo (-w i) (w i))
  have hsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx i hi
    have hxi := hx i hi
    change -w i < -x i ∧ -x i < w i
    constructor <;> linarith [hxi.1, hxi.2]
  have hconv : Convex ℝ S := convex_pi (by intro i hi; exact convex_Ioo _ _)
  have hvol : volume S ≤ volume F * 2 ^ Module.finrank ℝ (ι → ℝ) := by
    by_contra h
    obtain ⟨x, hx, hxS⟩ :=
      exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
        hF hsymm hconv (lt_of_not_ge h)
    apply hx
    apply hempty x
    intro i
    exact abs_lt.mpr (hxS i (Set.mem_univ i))
  simpa [S, Real.volume_pi_Ioo, sub_neg_eq_add, ← two_mul,
    Module.finrank_pi] using hvol

theorem width_product_le {ι : Type*} [Fintype ι]
    (L : AddSubgroup (ι → ℝ)) [Countable L] (F : Set (ι → ℝ))
    (hF : IsAddFundamentalDomain L F volume) (hfinite : volume F ≠ ⊤)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hempty : ∀ x : L, (∀ i, |(x : ι → ℝ) i| < w i) → x = 0) :
    (∏ i, w i) ≤ volume.real F := by
  have he := box_volume_le L F hF w hempty
  have ht : volume F * 2 ^ Fintype.card ι ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono ht he
  have hreal (i : ι) : (ENNReal.ofReal (2 * w i)).toReal = 2 * w i :=
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hw i))
  simp only [ENNReal.toReal_prod, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, hreal] at hr
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hr
  have hp : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  change (∏ i, w i) ≤ (volume F).toReal
  nlinarith

theorem successive_box_empty {n : ℕ} (hn : 0 < n)
    (L : AddSubgroup (Fin n → ℝ)) (ℓ : Fin n → ℝ)
    (hpositive : ∀ i, 0 < ℓ i) (hmono : Monotone ℓ)
    (hlength : ∀ (x : L) (j : Fin n), (x : Fin n → ℝ) j ≠ 0 →
      (∀ i, j < i → (x : Fin n → ℝ) i = 0) →
      ℓ j ^ 2 ≤ ∑ i, (x : Fin n → ℝ) i ^ 2) :
    ∀ x : L, (∀ i, |(x : Fin n → ℝ) i| < ℓ i / Real.sqrt n) → x = 0 := by
  classical
  intro x hx
  by_contra hx0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  let S : Finset (Fin n) := Finset.univ.filter (fun i => (x : Fin n → ℝ) i ≠ 0)
  have hS : S.Nonempty := by
    by_contra hs
    apply hx0
    apply Subtype.ext
    funext i
    have hi : i ∉ S := by simp [Finset.not_nonempty_iff_eq_empty.mp hs]
    simpa [S] using hi
  let j := S.max' hS
  have hj : (x : Fin n → ℝ) j ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have hlast : ∀ i, j < i → (x : Fin n → ℝ) i = 0 := by
    intro i hji
    by_contra hi
    have himem : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hij : i ≤ j := S.le_max' i himem
    exact (not_lt_of_ge hij) hji
  have hb (i : Fin n) : |(x : Fin n → ℝ) i| < ℓ j / Real.sqrt n := by
    by_cases hij : i ≤ j
    · exact lt_of_lt_of_le (hx i) ((div_le_div_iff_of_pos_right hc).mpr (hmono hij))
    · rw [hlast i (lt_of_not_ge hij), abs_zero]
      exact div_pos (hpositive j) hc
  have hsq (i : Fin n) : (x : Fin n → ℝ) i ^ 2 < (ℓ j / Real.sqrt n) ^ 2 := by
    apply sq_lt_sq.mpr
    rw [abs_of_pos (div_pos (hpositive j) hc)]
    exact hb i
  have hsum := Finset.sum_lt_sum_of_nonempty
    (s := Finset.univ) (⟨j, Finset.mem_univ j⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
    (fun i _ => hsq i)
  have heq : (n : ℝ) * (ℓ j / Real.sqrt n) ^ 2 = ℓ j ^ 2 := by
    rw [div_pow, Real.sq_sqrt hnR.le]
    field_simp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [heq] at hsum
  exact (not_lt_of_ge (hlength x j hj hlast)) hsum

theorem successive_product_le {n : ℕ} (hn : 0 < n)
    (L : AddSubgroup (Fin n → ℝ)) [Countable L] (F : Set (Fin n → ℝ))
    (hF : IsAddFundamentalDomain L F volume) (hfinite : volume F ≠ ⊤)
    (ℓ : Fin n → ℝ) (hpositive : ∀ i, 0 < ℓ i) (hmono : Monotone ℓ)
    (hlength : ∀ (x : L) (j : Fin n), (x : Fin n → ℝ) j ≠ 0 →
      (∀ i, j < i → (x : Fin n → ℝ) i = 0) →
      ℓ j ^ 2 ≤ ∑ i, (x : Fin n → ℝ) i ^ 2) :
    (∏ i, ℓ i) ≤ Real.sqrt n ^ n * volume.real F := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hw (i : Fin n) : 0 ≤ ℓ i / Real.sqrt n := (div_pos (hpositive i) hc).le
  have hprod := width_product_le L F hF hfinite
    (fun i => ℓ i / Real.sqrt n) hw (successive_box_empty hn L ℓ hpositive hmono hlength)
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hpow : 0 < Real.sqrt n ^ n := pow_pos hc n
  exact (div_le_iff₀ hpow).mp hprod |>.trans_eq (mul_comm _ _)

end Problem355.SuccessiveBox

end OAI
