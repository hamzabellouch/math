import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveFinite

namespace OAI

/-! # Restriction and monotonicity for the actual quadratic-sieve matrix -/

namespace Ostmann

open scoped BigOperators Classical

 theorem oddSquarefreeRange_mono {N R : ℕ} (h : N ≤ R) :
    oddSquarefreeRange N ⊆ oddSquarefreeRange R := by
  intro n hn
  obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hrange).1, (Finset.mem_Icc.mp hrange).2.trans h⟩, hodd, hsq⟩

 theorem QuadraticSieveBound.mono_constant {M N : ℕ} {K L : ℝ}
    (h : QuadraticSieveBound M N K) (hKL : K ≤ L) : QuadraticSieveBound M N L := by
  intro b
  exact (h b).trans (mul_le_mul_of_nonneg_right hKL
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

 theorem QuadraticSieveBound.mono_first {M R N : ℕ} {K : ℝ}
    (hMR : M ≤ R) (h : QuadraticSieveBound R N K) : QuadraticSieveBound M N K := by
  intro b
  apply le_trans _ (h b)
  exact Finset.sum_le_sum_of_subset_of_nonneg (oddSquarefreeRange_mono hMR)
    (fun _ _ _ => sq_nonneg _)

 theorem quadraticSieveSum_restrict {N R : ℕ} (hNR : N ≤ R) (b : ℕ → ℂ) (m : ℕ) :
    quadraticSieveSum R (fun n => if n ∈ oddSquarefreeRange N then b n else 0) m =
      quadraticSieveSum N b m := by
  have hs := Finset.sum_subset (oddSquarefreeRange_mono hNR)
    (f := fun n => (if n ∈ oddSquarefreeRange N then b n else 0) * (jacobiSym (n : ℤ) m : ℂ))
    (by intro n _ hn; simp [hn])
  simpa only [Finset.sum_ite_mem, ite_mul, zero_mul, Finset.inter_self, quadraticSieveSum] using hs.symm

 theorem quadraticSieveEnergy_restrict {N R : ℕ} (hNR : N ≤ R) (b : ℕ → ℂ) :
    quadraticSieveEnergy R (fun n => if n ∈ oddSquarefreeRange N then b n else 0) =
      quadraticSieveEnergy N b := by
  have hs := Finset.sum_subset (oddSquarefreeRange_mono hNR)
    (f := fun n => ‖(if n ∈ oddSquarefreeRange N then b n else 0)‖ ^ 2)
    (by intro n _ hn; simp [hn])
  simpa only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_ite_mem, Finset.inter_self, quadraticSieveEnergy] using hs.symm

 theorem QuadraticSieveBound.mono_second {M N R : ℕ} {K : ℝ}
    (hNR : N ≤ R) (h : QuadraticSieveBound M R K) : QuadraticSieveBound M N K := by
  intro b
  have hh := h (fun n => if n ∈ oddSquarefreeRange N then b n else 0)
  simpa only [quadraticSieveSum_restrict hNR, quadraticSieveEnergy_restrict hNR] using hh

end Ostmann

end OAI
