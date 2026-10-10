import OAI.NumberTheory.Ostmann.Quadratic.KernelPopulationCollision
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSplitRoot

namespace OAI

/-! # The collision contradiction on the actual quadratic split primes -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def quadraticSplitPrimes (P : Finset ℕ) (m : ℕ) (u v : ℤ) : Finset ℕ :=
  P.filter fun p => ¬p ∣ 2 * m * u.natAbs * v.natAbs ∧ jacobiSym (u * v) p = 1

theorem quadratic_split_avoid (P : Finset ℕ) (m : ℕ) (u v : ℤ)
    {p : ℕ} (hp : p ∈ quadraticSplitPrimes P m u v) :
    ¬p ∣ m ∧ ¬p ∣ u.natAbs ∧ ¬p ∣ v.natAbs := by
  have hn := (Finset.mem_filter.mp hp).2.1
  constructor
  · intro hd
    apply hn
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 2) _) _
  constructor
  · intro hd
    apply hn
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd (2 * m)) _
  · intro hd
    exact hn (dvd_mul_of_dvd_right hd _)

/-- No choice of a square root is assumed: Jacobi splitting constructs the
rescaling and hence the disjoint residue populations at every retained prime. -/
theorem quadratic_kernel_collision_bound (P : Finset ℕ) (S T : Finset ℤ)
    (hSnon : S.Nonempty) (hTnon : T.Nonempty)
    (rootS rootT : ℤ → ℕ) (m Ds Dt : ℕ) (hm : 0 < m)
    (hDs : 1 ≤ Ds) (hDt : 1 ≤ Dt) (h u v : ℤ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hS : ∀ x ∈ S, u * (rootS x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hT : ∀ y ∈ T, v * (rootT y : ℤ) ^ 2 = (m : ℤ) * y - h)
    (X : ℝ) (hspanS : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X)
    (hspanT : ∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ X)
    (hdiamS : Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) ≤ Ds)
    (hdiamT : Real.sqrt ((m : ℝ) * X / |(v : ℝ)|) ≤ Dt)
    (hprimeDiff : ∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime)
    (L η C : ℝ) (hP : ∀ p ∈ P, p.Prime)
    (hsmall : ∀ p ∈ P, ∀ x ∈ S, ∀ y ∈ T, p < (x - y).natAbs)
    (hL : 0 ≤ L) (hη : η ≤ 1 / 1000)
    (hmertens : (1 / 2 - 5 * η) * L - C ≤ ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ))
    (hsplitmass : (3 / 100) * L ≤
      ∑ p ∈ quadraticSplitPrimes P m u v, Real.log (p : ℝ) / (p : ℝ))
    (hbudget : Real.log (Ds : ℝ) + Real.log (Dt : ℝ) +
      (1 / (S.card : ℝ) + 1 / (T.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) ≤
        (101 / 100) * L) : L ≤ 50 * C := by
  let R := quadraticSplitPrimes P m u v
  have hRP : R ⊆ P := Finset.filter_subset _ _
  have hex (p : R) : ∃ c : ZMod (p : ℕ), (u : ZMod (p : ℕ)) * c ^ 2 = (v : ZMod (p : ℕ)) :=
    exists_quadratic_split_root u v (hP p (hRP p.property))
      (quadratic_split_avoid P m u v p.property).2.1
      (Finset.mem_filter.mp p.property).2.2
  choose c hc using hex
  let c' (p : ℕ) : ZMod p := if hp : p ∈ R then c ⟨p, hp⟩ else 0
  apply kernel_populations_scale_bound P R S T hSnon hTnon rootS rootT m Ds Dt hm hDs hDt
    h u v hu hv hS hT X hspanS hspanT hdiamS hdiamT hprimeDiff L η C hRP hP c'
  · intro p hp
    simpa only [c', dite_eq_left hp] using hc ⟨p, hp⟩
  · intro p hp
    exact (quadratic_split_avoid P m u v hp).1
  · intro p hp
    exact (quadratic_split_avoid P m u v hp).2.2
  · intro p hp
    exact hsmall p (hRP hp)
  · exact hL
  · exact hη
  · exact hmertens
  · exact hsplitmass
  · exact hbudget

end Ostmann

end OAI
