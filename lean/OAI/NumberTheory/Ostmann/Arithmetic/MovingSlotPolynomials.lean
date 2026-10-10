import OAI.NumberTheory.Ostmann.Arithmetic.MovingLineComparison

namespace OAI

/-! # Actual slot products in the moving-giant line polynomials

Lists retain multiplicities: an ancestral compensation prime may occur in
several descendant regular products. No squarefree polynomial is substituted.
-/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def movingSlotProduct {σ : Type*} (slots : List σ) : MvPolynomial σ ℤ :=
  (slots.map MvPolynomial.X).prod

noncomputable def movingSlotCoefficient {σ : Type*} (s : ℤ) (slots : List σ) :
    MvPolynomial σ ℤ := MvPolynomial.C s * movingSlotProduct slots

theorem movingSlotProduct_eval {σ R : Type*} [CommRing R]
    (f : ℤ →+* R) (x : σ → R) (slots : List σ) :
    MvPolynomial.eval₂Hom f x (movingSlotProduct slots) = (slots.map x).prod := by
  induction slots with
  | nil => simp [movingSlotProduct]
  | cons i slots ih => simpa [movingSlotProduct] using congrArg (x i * ·) ih

theorem movingSlotCoefficient_eval {σ R : Type*} [CommRing R]
    (f : ℤ →+* R) (x : σ → R) (s : ℤ) (slots : List σ) :
    MvPolynomial.eval₂Hom f x (movingSlotCoefficient s slots) =
      f s * (slots.map x).prod := by
  simp only [movingSlotCoefficient, map_mul, MvPolynomial.eval₂Hom_C,
    movingSlotProduct_eval]

theorem movingSlotProduct_degree {σ : Type*} (slots : List σ) :
    (movingSlotProduct slots).totalDegree ≤ slots.length := by
  induction slots with
  | nil => simp [movingSlotProduct]
  | cons i slots ih =>
    change (MvPolynomial.X i * movingSlotProduct slots).totalDegree ≤ slots.length + 1
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      rw [MvPolynomial.totalDegree_X]
      omega)

theorem movingSlotCoefficient_degree {σ : Type*} (s : ℤ) (slots : List σ) :
    (movingSlotCoefficient s slots).totalDegree ≤ slots.length := by
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using movingSlotProduct_degree slots)

theorem movingSlotProduct_vars {σ : Type*} [DecidableEq σ] (slots : List σ) :
    (movingSlotProduct slots).vars ⊆ slots.toFinset := by
  induction slots with
  | nil => simp [movingSlotProduct]
  | cons i slots ih =>
    intro j hj
    have h := MvPolynomial.vars_mul (MvPolynomial.X i) (movingSlotProduct slots) hj
    rcases Finset.mem_union.mp h with h | h
    · have hji : j = i := by
        simpa only [MvPolynomial.vars_X, Finset.mem_singleton] using h
      simp [hji]
    · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (ih h)))

theorem movingSlotCoefficient_vars {σ : Type*} [DecidableEq σ] (s : ℤ) (slots : List σ) :
    (movingSlotCoefficient s slots).vars ⊆ slots.toFinset := by
  intro i hi
  have h := MvPolynomial.vars_mul (MvPolynomial.C s) (movingSlotProduct slots) hi
  rcases Finset.mem_union.mp h with h | h
  · rw [MvPolynomial.vars_C] at h
    exact (Finset.notMem_empty _ h).elim
  · exact movingSlotProduct_vars slots h

theorem movingSlotProduct_abs_le {σ : Type*} (x : σ → ℝ) (slots : List σ)
    (T : ℝ) (hT : 0 ≤ T) (hx : ∀ i ∈ slots, |x i| ≤ T) :
    |(slots.map x).prod| ≤ T ^ slots.length := by
  induction slots with
  | nil => simp
  | cons i slots ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul, List.length_cons, pow_succ]
    calc
      |x i| * |(slots.map x).prod| ≤ T * T ^ slots.length :=
        mul_le_mul (hx i (by simp)) (ih fun j hj => hx j (by simp [hj]))
          (abs_nonneg _) hT
      _ = _ := mul_comm _ _

theorem movingSlotCoefficient_abs_le {σ : Type*} (x : σ → ℝ) (s : ℤ)
    (slots : List σ) (F T : ℝ) (hF : |(s : ℝ)| ≤ F) (hT : 0 ≤ T)
    (hx : ∀ i ∈ slots, |x i| ≤ T) :
    |MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x (movingSlotCoefficient s slots)| ≤
      F * T ^ slots.length := by
  rw [movingSlotCoefficient_eval, abs_mul]
  exact mul_le_mul hF (movingSlotProduct_abs_le x slots T hT hx)
    (abs_nonneg _) (le_trans (abs_nonneg _) hF)

theorem movingSlotCoefficient_ne_zero {σ K : Type*} [Field K]
    (x : σ → K) (s : ℤ) (slots : List σ)
    (hs : (s : K) ≠ 0) (hx : ∀ i ∈ slots, x i ≠ 0) :
    MvPolynomial.eval₂Hom (Int.castRingHom K) x (movingSlotCoefficient s slots) ≠ 0 := by
  rw [movingSlotCoefficient_eval]
  apply mul_ne_zero hs
  induction slots with
  | nil => simp
  | cons i slots ih =>
    exact mul_ne_zero (hx i (by simp)) (ih fun j hj => hx j (by simp [hj]))

/-- The products multiplying the current two giants, together with the actual
compensation product in the denominator. Giants themselves are excluded. -/
structure MovingSlotReversal (σ : Type*) where
  left : Bool
  rootFrequency : ℤ
  leftFrequency : ℤ
  rightFrequency : ℤ
  leftSlots : List σ
  rightSlots : List σ
  compensationSlots : List σ

namespace MovingSlotReversal

noncomputable def polynomial {σ : Type*} (s : MovingSlotReversal σ) : PolynomialReversal σ where
  left := s.left
  v := movingSlotCoefficient s.leftFrequency s.rightSlots
  w := movingSlotCoefficient s.rightFrequency s.leftSlots
  u := movingSlotCoefficient s.rootFrequency s.compensationSlots

def lengthLE {σ : Type*} (s : MovingSlotReversal σ) (d : ℕ) : Prop :=
  s.rightSlots.length ≤ d ∧ s.leftSlots.length ≤ d ∧ s.compensationSlots.length ≤ d

def frequencyLE {σ : Type*} (s : MovingSlotReversal σ) (F : ℝ) : Prop :=
  |(s.leftFrequency : ℝ)| ≤ F ∧ |(s.rightFrequency : ℝ)| ≤ F ∧
    |(s.rootFrequency : ℝ)| ≤ F

theorem polynomial_degree {σ : Type*} (s : MovingSlotReversal σ) (d : ℕ)
    (h : s.lengthLE d) :
    s.polynomial.v.totalDegree ≤ d ∧ s.polynomial.w.totalDegree ≤ d ∧
      s.polynomial.u.totalDegree ≤ d :=
  ⟨(movingSlotCoefficient_degree _ _).trans h.1,
   (movingSlotCoefficient_degree _ _).trans h.2.1,
   (movingSlotCoefficient_degree _ _).trans h.2.2⟩

theorem polynomial_height {σ : Type*} (s : MovingSlotReversal σ) (x : σ → ℝ)
    (F T : ℝ) (d : ℕ) (hF : s.frequencyLE F) (hT : 1 ≤ T)
    (hd : s.lengthLE d) (hx : ∀ i, |x i| ≤ T) :
    let φ := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x
    |φ s.polynomial.v| ≤ F * T ^ d ∧ |φ s.polynomial.w| ≤ F * T ^ d ∧
      |φ s.polynomial.u| ≤ F * T ^ d := by
  have hF0 : 0 ≤ F := (abs_nonneg _).trans hF.1
  have hb (a : ℤ) (slots : List σ) (ha : |(a : ℝ)| ≤ F) (hlen : slots.length ≤ d) :
      |MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x (movingSlotCoefficient a slots)| ≤ F * T ^ d :=
    (movingSlotCoefficient_abs_le x a slots F T ha (by linarith) (fun i _ => hx i)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT hlen) hF0)
  exact ⟨hb _ _ hF.1 hd.1, hb _ _ hF.2.1 hd.2.1, hb _ _ hF.2.2 hd.2.2⟩

theorem polynomial_units {σ K : Type*} [Field K] (s : MovingSlotReversal σ)
    (x : σ → K) (hfreq : (s.leftFrequency : K) ≠ 0 ∧
      (s.rightFrequency : K) ≠ 0 ∧ (s.rootFrequency : K) ≠ 0)
    (hx : ∀ i, x i ≠ 0) :
    let φ := MvPolynomial.eval₂Hom (Int.castRingHom K) x
    φ s.polynomial.v ≠ 0 ∧ φ s.polynomial.w ≠ 0 ∧ φ s.polynomial.u ≠ 0 :=
  ⟨movingSlotCoefficient_ne_zero x _ _ hfreq.1 (fun i _ => hx i),
   movingSlotCoefficient_ne_zero x _ _ hfreq.2.1 (fun i _ => hx i),
   movingSlotCoefficient_ne_zero x _ _ hfreq.2.2 (fun i _ => hx i)⟩

end MovingSlotReversal
end Ostmann

end OAI
