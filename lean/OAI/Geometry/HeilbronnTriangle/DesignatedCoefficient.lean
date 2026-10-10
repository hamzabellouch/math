import OAI.Geometry.HeilbronnTriangle.DigitEncoding

namespace OAI


noncomputable section

namespace Problem355.DesignatedCoefficient

open Polynomial

def position (T : ℕ) (i : Fin 3) (a : Fin T) : ℕ :=
  ![a.val, T * a.val, T ^ 2 - (T + 1) * a.val] i

theorem position_sum_matching (T : ℕ) (v : Fin 3 → Fin T) :
    position T 0 (v 0) + position T 1 (v 1) + position T 2 (v 2) = T ^ 2 ↔
      v 0 = v 1 ∧ v 1 = v 2 := by
  have hle : (T + 1) * (v 2).val ≤ T ^ 2 := by
    have hv : (v 2).val + 1 ≤ T := (v 2).isLt
    have hh := Nat.mul_le_mul_left (T + 1) hv
    nlinarith
  have hsub := Nat.sub_add_cancel hle
  change (v 0).val + T * (v 1).val + (T ^ 2 - (T + 1) * (v 2).val) = T ^ 2 ↔
    v 0 = v 1 ∧ v 1 = v 2
  constructor
  · intro h
    have hm := DigitEncoding.matched_indices (v 0).isLt (v 2).isLt
      (show (v 0).val + T * (v 1).val = (T + 1) * (v 2).val by omega)
    exact ⟨Fin.ext (hm.1.trans hm.2.symm), Fin.ext hm.2⟩
  · rintro ⟨h01, h12⟩
    have hv0 : (v 0).val = (v 2).val := congrArg Fin.val (h01.trans h12)
    have hv1 : (v 1).val = (v 2).val := congrArg Fin.val h12
    rw [hv0, hv1]
    nlinarith

theorem sum_diagonal {R : Type*} [AddCommMonoid R] (T : ℕ)
    (F : (Fin 3 → Fin T) → R) :
    (∑ v : Fin 3 → Fin T, if v 0 = v 1 ∧ v 1 = v 2 then F v else 0) =
      ∑ a : Fin T, F (fun _ => a) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun a _ => fun _ : Fin 3 => a)
  · intro a ha
    simp
  · intro a ha b hb hab
    exact congrFun hab 0
  · intro v hv
    rcases Finset.mem_filter.mp hv with ⟨_, h01, h12⟩
    refine ⟨v 0, Finset.mem_univ _, ?_⟩
    funext i
    fin_cases i <;> simp_all
  · intro a ha
    rfl

theorem det_monomial_rows {R : Type*} [CommRing R]
    (v : Fin 3 → ℕ) (A : Matrix (Fin 3) (Fin 3) R) :
    Matrix.det (Matrix.of (fun i j => monomial (v i) (A i j))) =
      monomial (v 0 + v 1 + v 2) A.det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, Polynomial.monomial_mul_monomial, map_add, map_sub]

def polynomialMatrix {R : Type*} [CommRing R] (T : ℕ)
    (f : Fin 3 → Fin T → Fin 3 → R) : Matrix (Fin 3) (Fin 3) R[X] :=
  fun i j => ∑ a : Fin T, monomial (position T i a) (f i a j)

theorem designated_coefficient {R : Type*} [CommRing R] (T : ℕ)
    (f : Fin 3 → Fin T → Fin 3 → R) :
    (Matrix.det (polynomialMatrix T f)).coeff (T ^ 2) =
      ∑ a : Fin T, Matrix.det (Matrix.of (fun i j => f i a j)) := by
  classical
  have hm := (Matrix.detRowAlternating (n := Fin 3) (R := R[X])).toMultilinearMap.map_sum_finset
    (fun i (a : Fin T) j => monomial (position T i a) (f i a j))
    (fun _ => Finset.univ)
  change Matrix.det (Matrix.of (fun i => ∑ a : Fin T, fun j =>
    monomial (position T i a) (f i a j))) = _ at hm
  have hrows : (fun i => ∑ a : Fin T, fun j =>
      monomial (position T i a) (f i a j)) = polynomialMatrix T f := by
    funext i j
    simp only [Finset.sum_apply, polynomialMatrix]
  rw [hrows, Fintype.piFinset_univ] at hm
  change (polynomialMatrix T f).det = _ at hm
  rw [hm, Polynomial.finsetSum_coeff]
  change (∑ v : Fin 3 → Fin T,
    (Matrix.det (Matrix.of (fun i j => monomial (position T i (v i)) (f i (v i) j)))).coeff
      (T ^ 2)) = _
  calc
    _ = ∑ v : Fin 3 → Fin T,
        if v 0 = v 1 ∧ v 1 = v 2 then Matrix.det (Matrix.of (fun i j => f i (v i) j)) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      have hdet := det_monomial_rows (fun i => position T i (v i))
        (Matrix.of (fun i j => f i (v i) j))
      simp only [Matrix.of_apply] at hdet
      rw [hdet, Polynomial.coeff_monomial]
      by_cases h : v 0 = v 1 ∧ v 1 = v 2
      · have hp := (position_sum_matching T v).mpr h
        rw [ite_eq_left hp, ite_eq_left h]
      · have hp : ¬ (position T 0 (v 0) + position T 1 (v 1) +
            position T 2 (v 2) = T ^ 2) := fun hp => h ((position_sum_matching T v).mp hp)
        rw [ite_eq_right hp, ite_eq_right h]
    _ = _ := sum_diagonal T (fun v => Matrix.det (Matrix.of (fun i j => f i (v i) j)))

theorem map_designated_coefficient {R : Type*} [CommRing R] (φ : ℤ →+* R)
    (T : ℕ) (P : Matrix (Fin 3) (Fin 3) ℤ[X])
    (f : Fin 3 → Fin T → Fin 3 → R)
    (hmap : ∀ i j, (P i j).map φ = polynomialMatrix T f i j) :
    φ (P.det.coeff (T ^ 2)) = ∑ a : Fin T, Matrix.det (Matrix.of (fun i j => f i a j)) := by
  have hm : P.det.map φ = Matrix.det (Matrix.of (fun i j => (P i j).map φ)) :=
    (Polynomial.mapRingHom φ).map_det P
  have hmatrix : (fun i j => (P i j).map φ) = polynomialMatrix T f := by
    funext i j
    exact hmap i j
  rw [hmatrix] at hm
  rw [← Polynomial.coeff_map, hm]
  exact designated_coefficient T f

theorem designated_coefficient_ne_zero {R : Type*} [CommRing R] (φ : ℤ →+* R)
    (T : ℕ) (P : Matrix (Fin 3) (Fin 3) ℤ[X])
    (f : Fin 3 → Fin T → Fin 3 → R)
    (hmap : ∀ i j, (P i j).map φ = polynomialMatrix T f i j)
    (hne : (∑ a : Fin T, Matrix.det (Matrix.of (fun i j => f i a j))) ≠ 0) :
    P.det.coeff (T ^ 2) ≠ 0 := by
  intro hz
  apply hne
  rw [← map_designated_coefficient φ T P f hmap, hz, map_zero]

end Problem355.DesignatedCoefficient

end

end OAI
