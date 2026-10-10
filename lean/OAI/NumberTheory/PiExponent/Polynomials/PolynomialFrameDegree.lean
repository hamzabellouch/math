import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Complex.Basic

namespace OAI

namespace PiExponentApprox

noncomputable section

open MvPolynomial

def monomialWeight {m : ℕ} (w : Fin (m + 1) → ℝ)
    (d : Fin (m + 1) →₀ ℕ) : ℝ :=
  ∑ i, (d i : ℝ) * w i

def HasWeightedDegreeLE {m : ℕ} (w : Fin (m + 1) → ℝ) (N : ℝ)
    (p : MvPolynomial (Fin (m + 1)) ℂ) : Prop :=
  ∀ d ∈ p.support, monomialWeight w d ≤ N

theorem monomialWeight_add {m : ℕ} (w : Fin (m + 1) → ℝ)
    (d e : Fin (m + 1) →₀ ℕ) :
    monomialWeight w (d + e) = monomialWeight w d + monomialWeight w e := by
  simp [monomialWeight, Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem monomialWeight_single {m : ℕ} (w : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) : monomialWeight w (Finsupp.single i 1) = w i := by
  classical
  simp [monomialWeight, Finsupp.single_apply]

theorem HasWeightedDegreeLE.zero {m : ℕ} (w : Fin (m + 1) → ℝ) (N : ℝ) :
    HasWeightedDegreeLE w N (0 : MvPolynomial (Fin (m + 1)) ℂ) := by
  simp [HasWeightedDegreeLE]

theorem HasWeightedDegreeLE.mono {m : ℕ} {w : Fin (m + 1) → ℝ} {N M : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (hNM : N ≤ M) : HasWeightedDegreeLE w M p :=
  fun d hd => (hp d hd).trans hNM

theorem HasWeightedDegreeLE.add {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p q : MvPolynomial (Fin (m + 1)) ℂ}
    (hp : HasWeightedDegreeLE w N p) (hq : HasWeightedDegreeLE w N q) :
    HasWeightedDegreeLE w N (p + q) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
  · exact hp d hd
  · exact hq d hd

theorem HasWeightedDegreeLE.sum {m : ℕ} {α : Type*} {w : Fin (m + 1) → ℝ}
    {N : ℝ} (s : Finset α) (p : α → MvPolynomial (Fin (m + 1)) ℂ)
    (hp : ∀ a ∈ s, HasWeightedDegreeLE w N (p a)) :
    HasWeightedDegreeLE w N (∑ a ∈ s, p a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasWeightedDegreeLE.zero w N
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hp a (Finset.mem_insert_self a s)).add
        (ih (fun b hb => hp b (Finset.mem_insert_of_mem hb)))

theorem pderiv_support_shift {m : ℕ} (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) ℂ) (d : Fin (m + 1) →₀ ℕ)
    (hd : d ∈ (MvPolynomial.pderiv i p).support) : d + Finsupp.single i 1 ∈ p.support := by
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  apply hcoeff
  rw [MvPolynomial.coeff_pderiv, hz, zero_mul]

theorem HasWeightedDegreeLE.pderiv {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w (N - w i) (MvPolynomial.pderiv i p) := by
  intro d hd
  apply (le_sub_iff_add_le).mpr
  have h := hp (d + Finsupp.single i 1) (pderiv_support_shift i p d hd)
  simpa only [monomialWeight_add, monomialWeight_single] using h

theorem HasWeightedDegreeLE.X_mul {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w (N + w i) (MvPolynomial.X i * p) := by
  intro d hd
  have hsupp := MvPolynomial.support_X_mul i p
  rw [hsupp] at hd
  obtain ⟨e, he, hed⟩ := Finset.mem_map.mp hd
  have heq : Finsupp.single i 1 + e = d := hed
  rw [← heq, monomialWeight_add, monomialWeight_single, add_comm (w i)]
  exact add_le_add (hp e he) (le_refl (w i))

theorem HasWeightedDegreeLE.X_mul_pderiv {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w N (MvPolynomial.X i * MvPolynomial.pderiv i p) := by
  simpa only [sub_add_cancel] using (hp.pderiv i).X_mul i

theorem HasWeightedDegreeLE.pderiv_preserves {m : ℕ} {w : Fin (m + 1) → ℝ}
    {N : ℝ} {p : MvPolynomial (Fin (m + 1)) ℂ}
    (hp : HasWeightedDegreeLE w N p) (i : Fin (m + 1)) (hi : 0 ≤ w i) :
    HasWeightedDegreeLE w N (MvPolynomial.pderiv i p) :=
  (hp.pderiv i).mono (sub_le_self N hi)

end

end PiExponentApprox

end OAI
