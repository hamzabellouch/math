import Mathlib
import OAI.Computability.QuantumFactoring.TriangularPaths

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators

lemma pathShift_prefix {A : Type*} [AddCommGroup A] {b : ℕ}
    (δ : Fin b → Bits b → A) (x y : Bits b) (k : ℕ) (hk : k ≤ b) :
    pathShift δ x y k hk =
      ∑ j : Fin k, δ (j.castLE hk) (hybrid x y (j.val+1)) := by
  induction k with
  | zero => simp [pathShift]
  | succ k ih =>
    rw [pathShift, ih (by omega), Fin.sum_univ_castSucc]
    rfl

lemma pathShift_full_sum {A : Type*} [AddCommGroup A] {b : ℕ}
    (δ : Fin b → Bits b → A) (x y : Bits b) :
    pathShift δ x y b le_rfl = ∑ j : Fin b, δ j (hybrid x y (j.val+1)) := by
  rw [pathShift_prefix]
  rfl

lemma pathWeight_prefix {b : ℕ} (x y : Bits b) (k : ℕ) (hk : k ≤ b) :
    pathWeight x y k hk = ∏ j : Fin k, hEntry (x (j.castLE hk)) (y (j.castLE hk)) := by
  induction k with
  | zero => simp [pathWeight]
  | succ k ih => rw [pathWeight, ih (by omega), Fin.prod_univ_castSucc]; rfl

def dot {b : ℕ} (x y : Bits b) : ℕ := ∑ i : Fin b, (x i).toNat*(y i).toNat

lemma hEntry_pow (a c : Bool) :
    hEntry a c = (-1:ℂ)^(a.toNat*c.toNat) * (Real.sqrt 2 : ℂ)⁻¹ := by
  cases a <;> cases c <;> simp [hEntry, div_eq_mul_inv]

lemma pathWeight_full {b : ℕ} (x y : Bits b) :
    pathWeight x y b le_rfl = (-1:ℂ)^dot x y * (Real.sqrt 2 : ℂ)⁻¹^b := by
  rw [pathWeight_prefix]
  simp only [hEntry_pow, Fin.castLE_refl, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

lemma selected_evolve {A : Type*} [AddCommGroup A] [Fintype A] {b : ℕ}
    (δ : Fin b → Bits b → A) (x y : Bits b) (χ : A → ℂ) :
    (∑ z, star (χ z) * evolve δ x χ b le_rfl y z) =
      pathWeight x y b le_rfl *
        ∑ z, star (χ (z+pathShift δ x y b le_rfl)) * χ z := by
  simp only [evolve_full]
  calc
    _ = pathWeight x y b le_rfl * ∑ z, star (χ z) * χ (z-pathShift δ x y b le_rfl) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by
      congr 1
      symm
      simpa only [Equiv.coe_addRight, add_sub_cancel_right] using
        Equiv.sum_comp (Equiv.addRight (pathShift δ x y b le_rfl))
          (fun z => star (χ z) * χ (z-pathShift δ x y b le_rfl))

/-- The input word is reversed physically, while the output wire j is k_j. -/
def inputNumber {b : ℕ} (x : Bits b) : ℕ := ∑ i, 2^(b-1-i.val)*(x i).toNat
def outputNumber {b : ℕ} (y : Bits b) : ℕ := ∑ j, 2^j.val*(y j).toNat

def lowTerm {b : ℕ} (x y : Bits b) (i j : Fin b) : ℕ :=
  if j.val < i.val then 2^(b-1-i.val+j.val)*(x i).toNat*(y j).toNat else 0

def highTerm {b : ℕ} (x y : Bits b) (i j : Fin b) : ℕ :=
  if i.val < j.val then 2^(j.val-i.val-1)*(x i).toNat*(y j).toNat else 0

lemma productTerm {b : ℕ} (x y : Bits b) (i j : Fin b) :
    (2^(b-1-i.val)*(x i).toNat) * (2^j.val*(y j).toNat) =
      lowTerm x y i j +
        (if i=j then 2^(b-1)*(x i).toNat*(y i).toNat else 0) +
          2^b*highTerm x y i j := by
  have he : (2^(b-1-i.val)*(x i).toNat) * (2^j.val*(y j).toNat) =
      2^(b-1-i.val+j.val)*(x i).toNat*(y j).toNat := by rw [pow_add]; ring
  rw [he]
  by_cases hij : i.val < j.val
  · have hn : i ≠ j := by intro h; subst j; omega
    have hw : b-1-i.val+j.val = b+(j.val-i.val-1) := by have := i.isLt; omega
    simp only [lowTerm, highTerm, ite_eq_right (by omega : ¬j.val < i.val), ite_eq_left hij,
      ite_eq_right hn, hw, pow_add]
    ring
  · by_cases hji : j.val < i.val
    · have hn : i ≠ j := by intro h; subst j; omega
      simp [lowTerm, highTerm, hij, hji, hn]
    · have heq : i=j := Fin.ext (by omega)
      subst j
      have hw : b-1-i.val+i.val = b-1 := by have := i.isLt; omega
      simp [lowTerm, highTerm, hw]

lemma product_decomposition {b : ℕ} (x y : Bits b) :
    inputNumber x * outputNumber y =
      (∑ i, ∑ j, lowTerm x y i j) + 2^(b-1)*dot x y +
        2^b*(∑ i, ∑ j, highTerm x y i j) := by
  unfold inputNumber outputNumber
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, productTerm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [dot, Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- One shift after H_j combines all the prescribed mutually commuting
controlled power-of-two shifts in that row. -/
def rowShift {b : ℕ} (j : Fin b) (z : Bits b) : ℕ :=
  ∑ i, if j.val < i.val then 2^(b-1-i.val+j.val)*(z i).toNat*(z j).toNat else 0

lemma rowShift_hybrid {b : ℕ} (x y : Bits b) (j : Fin b) :
    rowShift j (hybrid x y (j.val+1)) = ∑ i, lowTerm x y i j := by
  unfold rowShift
  apply Finset.sum_congr rfl
  intro i _
  unfold lowTerm
  by_cases hi : j.val < i.val
  · simp [hi, hybrid, show ¬i.val < j.val+1 by omega]
  · simp [hi]

lemma pathShift_rows {A : Type*} [Ring A]
    {b : ℕ} (x y : Bits b) :
    pathShift (fun j z => (rowShift j z : A)) x y b le_rfl =
      ((∑ i, ∑ j, lowTerm x y i j : ℕ) : A) := by
  rw [pathShift_full_sum]
  simp only [rowShift_hybrid, Nat.cast_sum]
  exact Finset.sum_comm

end ExactQuantumFactoring.Triangular


end

end OAI
