import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiMomentReindex

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem primeSubsetProduct_gcd {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (s t : Finset P) :
    Nat.gcd (primeSubsetProduct s) (primeSubsetProduct t) = primeSubsetProduct (s ∩ t) := by
  have hs := primeSubsetProduct_squarefree hP s
  have ht := primeSubsetProduct_squarefree hP t
  have hg := hs.squarefree_of_dvd (Nat.gcd_dvd_left (primeSubsetProduct s) (primeSubsetProduct t))
  rw [← Nat.prod_primeFactors_of_squarefree hg, Nat.primeFactors_gcd hs.ne_zero ht.ne_zero,
    primeSubsetProduct_primeFactors hP, primeSubsetProduct_primeFactors hP,
    ← Finset.image_inter s t Subtype.val_injective, ← primeSubsetProduct_eq_image_prod]

theorem primeSubsetProduct_dvd_squarefree {L : ℕ} (hL : Squarefree L)
    (s : Finset L.primeFactors) : primeSubsetProduct s ∣ L := by
  rw [primeSubsetProduct_eq_image_prod]
  have hsub : s.image Subtype.val ⊆ L.primeFactors := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  exact (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hsub).trans
    (Nat.prod_primeFactors_of_squarefree hL).dvd

theorem sum_squarefree_divisors_eq_cube {A : Type*} [AddCommMonoid A]
    {L : ℕ} (hL : Squarefree L) (F : ℕ → A) :
    (∑ d ∈ L.divisors, F d) = ∑ s : Finset L.primeFactors, F (primeSubsetProduct s) := by
  classical
  have hP : ∀ p ∈ L.primeFactors, Nat.Prime p := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hSf : ∀ d ∈ L.divisors, Squarefree d := fun d hd =>
    hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hc : ∀ d ∈ L.divisors, d.primeFactors ⊆ L.primeFactors := fun d hd =>
    Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hL.ne_zero
  have hm (s : Finset L.primeFactors) : primeSubsetProduct s ∈ L.divisors :=
    Nat.mem_divisors.mpr ⟨primeSubsetProduct_dvd_squarefree hL s, hL.ne_zero⟩
  have hh := sum_primeSubsetProduct hP L.divisors hSf hc F
  simpa only [hm, ite_true] using hh.symm

theorem sqrt_primeSubsetProduct {P : Finset ℕ} (s : Finset P) :
    Real.sqrt (primeSubsetProduct s : ℝ) = ∏ p ∈ s, Real.sqrt (p.val : ℝ) := by
  simp only [primeSubsetProduct, Nat.cast_prod]
  exact Real.sqrt_prod s (fun p hp => Nat.cast_nonneg _)

theorem subset_weight_div_sqrt_product {P : Finset ℕ} (s : Finset P) (lam : ℝ) :
    lam ^ s.card / Real.sqrt (primeSubsetProduct s : ℝ) =
      ∏ p ∈ s, lam / Real.sqrt (p.val : ℝ) := by
  rw [Finset.prod_div_distrib, Finset.prod_const, sqrt_primeSubsetProduct]

end Ostmann.QuadraticCenter

end OAI
