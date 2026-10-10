import Mathlib

namespace OAI


namespace Problem355.LatticeCoordinates

open scoped BigOperators
open Matrix

variable {n : Type*} [finiteIndex : Fintype n] [decidableIndex : DecidableEq n]

theorem relIndex_nsmul_mem_span {n : Type*} [Fintype n] [DecidableEq n] (V : Matrix n n ℝ)
    (Λ : Submodule ℤ (n → ℝ)) {u : n → ℝ} (hu : u ∈ Λ) :
    (Submodule.span ℤ (Set.range V)).toAddSubgroup.relIndex Λ.toAddSubgroup • u ∈
      Submodule.span ℤ (Set.range V) := by
  exact (Submodule.span ℤ (Set.range V)).toAddSubgroup.nsmul_relIndex_mem hu

theorem exists_integer_coordinates_of_mem_span {n : Type*} [Fintype n] [DecidableEq n] (V A : Matrix n n ℝ) (m : ℕ)
    (hA : ∀ i, m • A i ∈ Submodule.span ℤ (Set.range V)) :
    ∃ Q : Matrix n n ℤ, Q.map (Int.castRingHom ℝ) * V = (m : ℝ) • A := by
  classical
  choose Q hQ using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hA i)
  refine ⟨Matrix.of Q, ?_⟩
  ext i j
  have h := congrFun (hQ i) j
  simpa [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, nsmul_eq_mul,
    zsmul_eq_mul] using h

theorem exists_integer_coordinates (V A : Matrix n n ℝ)
    (Λ : Submodule ℤ (n → ℝ)) (hA : ∀ i, A i ∈ Λ) :
    ∃ Q : Matrix n n ℤ, Q.map (Int.castRingHom ℝ) * V =
      ((Submodule.span ℤ (Set.range V)).toAddSubgroup.relIndex
        Λ.toAddSubgroup : ℝ) • A := by
  apply exists_integer_coordinates_of_mem_span
  intro i
  exact relIndex_nsmul_mem_span V Λ (hA i)

theorem coordinates_eq_scaled_mul_inv (V A : Matrix n n ℝ) (m : ℝ)
    (hV : V.det ≠ 0) (Q : Matrix n n ℤ)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A) :
    Q.map (Int.castRingHom ℝ) = m • (A * V⁻¹) := by
  have h := congrArg (fun M : Matrix n n ℝ => M * V⁻¹) hQ
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv V (isUnit_iff_ne_zero.mpr hV),
    Matrix.smul_mul] using h

theorem coordinates_det (V A : Matrix n n ℝ) (m : ℝ)
    (hV : V.det ≠ 0) (Q : Matrix n n ℤ)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A) :
    (Q.det : ℝ) = m ^ Fintype.card n * A.det / V.det := by
  apply (eq_div_iff hV).mpr
  have h := congrArg Matrix.det hQ
  have hcast : (Q.map (Int.castRingHom ℝ)).det = (Q.det : ℝ) := by
    exact ((Int.castRingHom ℝ).map_det Q).symm
  rw [Matrix.det_mul, hcast, Matrix.det_smul] at h
  exact h

theorem coordinates_injective {n : Type*} [Fintype n] [DecidableEq n] (V A A' : Matrix n n ℝ) (m : ℝ)
    (hm : m ≠ 0) (Q : Matrix n n ℤ)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A)
    (hQ' : Q.map (Int.castRingHom ℝ) * V = m • A') : A = A' := by
  have h : m • A = m • A' := hQ.symm.trans hQ'
  exact (smul_right_injective _ hm) h

theorem abs_det_le_factorial_prod (V : Matrix n n ℝ) (R : n → ℝ)
    (hV : ∀ i j, |V i j| ≤ R i) :
    |V.det| ≤ (Nat.factorial (Fintype.card n) : ℝ) * ∏ i, R i := by
  calc
    |V.det| = ‖∑ σ : Equiv.Perm n, σ.sign • ∏ i, V (σ i) i‖ := by
      rw [← Matrix.det_apply, Real.norm_eq_abs]
    _ ≤ ∑ σ : Equiv.Perm n, ‖σ.sign • ∏ i, V (σ i) i‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ∏ i, |V (σ i) i| := by
      simp only [norm_units_zsmul, norm_prod, Real.norm_eq_abs]
    _ ≤ ∑ σ : Equiv.Perm n, ∏ i, R i := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [← Equiv.prod_comp σ R]
      exact Finset.prod_le_prod₀ (fun i hi => abs_nonneg _) (fun i hi => hV (σ i) i)
    _ = (Nat.factorial (Fintype.card n) : ℝ) * ∏ i, R i := by
      simp [Fintype.card_perm]

theorem coordinate_abs_bound (V : Matrix n n ℝ) (α u : n → ℝ)
    (R : n → ℝ) (X : ℝ) (hV : V.det ≠ 0)
    (hR : ∀ i j, |V i j| ≤ R i) (hu : ∀ j, |u j| ≤ X)
    (hα : ∑ i, α i • V i = u) (j : n) :
    |α j| ≤ ((Nat.factorial (Fintype.card n) : ℝ) * X *
      ∏ i ∈ Finset.univ.erase j, R i) / |V.det| := by
  have hdet : (V.updateRow j u).det = α j * V.det := by
    rw [← hα, Matrix.det_updateRow_sum, smul_eq_mul]
  have hbound := abs_det_le_factorial_prod (V.updateRow j u) (Function.update R j X) ?_
  · rw [hdet, abs_mul, Finset.prod_update_of_mem (Finset.mem_univ j)] at hbound
    apply (le_div_iff₀ (abs_pos.mpr hV)).mpr
    simpa [Finset.sdiff_singleton_eq_erase, mul_assoc] using hbound
  · intro i k
    by_cases hi : i = j
    · subst i
      simpa using hu k
    · simpa [Matrix.updateRow_ne hi, Function.update_of_ne hi] using hR i k

theorem coordinate_abs_bound_of_product_bound
    (V : Matrix n n ℝ) (α u R : n → ℝ) (X C : ℝ)
    (hV : V.det ≠ 0) (hR : ∀ i j, |V i j| ≤ R i)
    (hu : ∀ j, |u j| ≤ X) (hX : 0 ≤ X)
    (hα : ∑ i, α i • V i = u) (j : n) (hRj : 0 < R j)
    (hprod : (∏ i, R i) ≤ C * |V.det|) :
    |α j| ≤ (Nat.factorial (Fintype.card n) : ℝ) * C * X / R j := by
  have hd : 0 < |V.det| := abs_pos.mpr hV
  have hp : (∏ i ∈ Finset.univ.erase j, R i) / |V.det| ≤ C / R j := by
    apply (div_le_div_iff₀ hd hRj).mpr
    calc
      (∏ i ∈ Finset.univ.erase j, R i) * R j = ∏ i, R i := by
        rw [mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      _ ≤ C * |V.det| := hprod
  calc
    |α j| ≤ ((Nat.factorial (Fintype.card n) : ℝ) * X *
        ∏ i ∈ Finset.univ.erase j, R i) / |V.det| :=
      coordinate_abs_bound V α u R X hV hR hu hα j
    _ = ((Nat.factorial (Fintype.card n) : ℝ) * X) *
        ((∏ i ∈ Finset.univ.erase j, R i) / |V.det|) := by ring
    _ ≤ ((Nat.factorial (Fintype.card n) : ℝ) * X) * (C / R j) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (Nat.cast_nonneg _) hX)
    _ = (Nat.factorial (Fintype.card n) : ℝ) * C * X / R j := by ring

theorem integer_coordinates_entry_bound
    (V A : Matrix n n ℝ) (Q : Matrix n n ℤ) (m X C : ℝ) (R : n → ℝ)
    (hV : V.det ≠ 0) (hR : ∀ i j, |V i j| ≤ R i)
    (hA : ∀ i j, |A i j| ≤ X) (hX : 0 ≤ X)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A)
    (hprod : (∏ i, R i) ≤ C * |V.det|) (i j : n) (hRj : 0 < R j) :
    |(Q i j : ℝ)| ≤
      (Nat.factorial (Fintype.card n) : ℝ) * C * (|m| * X) / R j := by
  apply coordinate_abs_bound_of_product_bound V (fun k => (Q i k : ℝ))
    ((m • A) i) R (|m| * X) C hV hR _ (mul_nonneg (abs_nonneg _) hX)
    _ j hRj hprod
  · intro k
    change |m * A i k| ≤ |m| * X
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hA i k) (abs_nonneg _)
  · ext k
    have h := congrFun (congrFun hQ i) k
    simpa [Matrix.mul_apply, Matrix.map_apply] using h

theorem exists_coordinate_family (V : Matrix n n ℝ) (m : ℝ) (hm : m ≠ 0)
    (S : Finset (Matrix n n ℝ))
    (hS : ∀ A ∈ S, ∃ Q : Matrix n n ℤ,
      Q.map (Int.castRingHom ℝ) * V = m • A) :
    ∃ T : Finset (Matrix n n ℤ), T.card = S.card ∧
      (∀ Q ∈ T, ∃ A ∈ S, Q.map (Int.castRingHom ℝ) * V = m • A) ∧
      (∀ A ∈ S, ∃ Q ∈ T, Q.map (Int.castRingHom ℝ) * V = m • A) := by
  classical
  choose f hf using fun A : S => hS A A.property
  have hinj : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    apply coordinates_injective V A B m hm (f A) (hf A)
    rw [h]
    exact hf B
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro Q hQ
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨A, A.property, hf A⟩
  · intro A hA
    exact ⟨f ⟨A, hA⟩, Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_univ _, rfl⟩,
      hf ⟨A, hA⟩⟩

theorem coordinates_det_ne_zero (V A : Matrix n n ℝ) (m : ℝ)
    (hm : m ≠ 0) (hA : A.det ≠ 0) (Q : Matrix n n ℤ)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A) : Q.det ≠ 0 := by
  intro hzero
  have h := congrArg Matrix.det hQ
  have hcast : (Q.map (Int.castRingHom ℝ)).det = (Q.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det Q).symm
  rw [Matrix.det_mul, hcast, hzero, Int.cast_zero, zero_mul, Matrix.det_smul] at h
  exact (mul_ne_zero (pow_ne_zero _ hm) hA) h.symm

theorem euclidean_norm_le_of_coord_bound {n : Type*} [Fintype n] [DecidableEq n] (v : EuclideanSpace ℝ n) (B : ℝ)
    (hB : 0 ≤ B) (hv : ∀ i, |v i| ≤ B) :
    ‖v‖ ≤ Real.sqrt (Fintype.card n) * B := by
  have hsum : (∑ i, ‖v i‖ ^ 2) ≤ (Fintype.card n : ℝ) * B ^ 2 := by
    calc
      (∑ i, ‖v i‖ ^ 2) ≤ ∑ _i : n, B ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
      _ = (Fintype.card n : ℝ) * B ^ 2 := by simp
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤
        Real.sqrt ((Fintype.card n : ℝ) * B ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card n) * B := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB]

theorem integer_coordinates_column_bound
    (V A : Matrix n n ℝ) (Q : Matrix n n ℤ) (m X C : ℝ) (R : n → ℝ)
    (hV : V.det ≠ 0) (hR : ∀ i j, |V i j| ≤ R i)
    (hA : ∀ i j, |A i j| ≤ X) (hX : 0 ≤ X) (hC : 0 ≤ C)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A)
    (hprod : (∏ i, R i) ≤ C * |V.det|) (j : n) (hRj : 0 < R j) :
    ‖(WithLp.toLp 2 (fun i => (Q i j : ℝ)) : EuclideanSpace ℝ n)‖ ≤
      Real.sqrt (Fintype.card n) *
        ((Nat.factorial (Fintype.card n) : ℝ) * C * (|m| * X) / R j) := by
  apply euclidean_norm_le_of_coord_bound
  · positivity
  · intro i
    exact integer_coordinates_entry_bound V A Q m X C R hV hR hA hX hQ hprod i j hRj

theorem exists_fixed_det_coordinate_family
    (V : Matrix n n ℝ) (m : ℕ) (hm : 0 < m) (R : n → ℝ) (X C : ℝ)
    (hV : V.det ≠ 0) (hR : ∀ i j, |V i j| ≤ R i)
    (hRpos : ∀ j, 0 < R j) (hX : 0 ≤ X) (hC : 0 ≤ C)
    (hprod : (∏ i, R i) ≤ C * |V.det|)
    (S : Finset (Matrix n n ℝ)) (hne : S.Nonempty)
    (hspan : ∀ A ∈ S, ∀ i, m • A i ∈ Submodule.span ℤ (Set.range V))
    (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X)
    (t : ℝ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    ∃ u : ℤ, u ≠ 0 ∧ (u : ℝ) = (m : ℝ) ^ Fintype.card n * t / V.det ∧
      ∃ T : Finset (Matrix n n ℤ), T.card = S.card ∧
        ∀ Q ∈ T, Q.det = u ∧ ∀ j,
          ‖(WithLp.toLp 2 (fun i => (Q i j : ℝ)) : EuclideanSpace ℝ n)‖ ≤
            Real.sqrt (Fintype.card n) *
              ((Nat.factorial (Fintype.card n) : ℝ) * C * ((m : ℝ) * X) / R j) := by
  classical
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  obtain ⟨T, hcard, hforward, hback⟩ := exists_coordinate_family V (m : ℝ) hmR S
    (fun A hA => exists_integer_coordinates_of_mem_span V A m (hspan A hA))
  obtain ⟨A₀, hA₀⟩ := hne
  obtain ⟨Q₀, hQ₀, hcoord₀⟩ := hback A₀ hA₀
  have ht₀ : A₀.det ≠ 0 := by rw [hdet A₀ hA₀]; exact ht
  have hdet₀ : (Q₀.det : ℝ) = (m : ℝ) ^ Fintype.card n * t / V.det := by
    simpa [hdet A₀ hA₀] using coordinates_det V A₀ (m : ℝ) hV Q₀ hcoord₀
  refine ⟨Q₀.det, coordinates_det_ne_zero V A₀ (m : ℝ) hmR ht₀ Q₀ hcoord₀,
    hdet₀, T, hcard, ?_⟩
  intro Q hQ
  obtain ⟨A, hA, hcoord⟩ := hforward Q hQ
  constructor
  · have hdetQ : (Q.det : ℝ) = (m : ℝ) ^ Fintype.card n * t / V.det := by
      simpa [hdet A hA] using coordinates_det V A (m : ℝ) hV Q hcoord
    exact_mod_cast hdetQ.trans hdet₀.symm
  · intro j
    simpa only [abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m)] using
      integer_coordinates_column_bound V A Q (m : ℝ) X C R hV hR
        (hbound A hA) hX hC hcoord hprod j (hRpos j)

end Problem355.LatticeCoordinates

end OAI
