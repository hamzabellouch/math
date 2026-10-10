import OAI.Algebra.OddKaplansky.AugmentBound

namespace OAI

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.FiniteMatrixInverse
noncomputable section
open scoped Classical BigOperators Matrix
variable {D : Type portUniverse1} {S : Type portUniverse2} [CommRing D] [Fintype S] [DecidableEq S]
lemma pow_entry_mem (I : Ideal D) (A : Matrix S S D) (hA : ∀ i j, A i j∈I) (n : ℕ) :
    ∀ i j, (A^n) i j∈I^n := by
  induction n with
  | zero => intro i j; simp
  | succ n ih =>
    intro i j
    rw [pow_succ A n,Matrix.mul_apply,pow_succ I n]
    apply Ideal.sum_mem
    intro k _
    exact Ideal.mul_mem_mul (ih i k) (hA k j)
lemma nilpotent_of_entries (I : Ideal D) (hI : IsNilpotent I)
    (A : Matrix S S D) (hA : ∀ i j, A i j∈I) : IsNilpotent A := by
  obtain ⟨n,hn⟩ := hI
  refine ⟨n,?_⟩
  funext i j
  have hh := pow_entry_mem I A hA n i j
  rw [hn] at hh
  exact hh

def series (N : Matrix S S D) (n : ℕ) := ∑ k ∈ Finset.range n, (-N)^k
lemma series_mul (N : Matrix S S D) (n : ℕ) (hN : N^n=0) : series N n*(1+N)=1 := by
  have hn : (-N)^n=0 := by rw [neg_pow,hN,mul_zero]
  simpa only [series,sub_neg_eq_add,hn,sub_zero] using geom_sum_mul_neg (-N) n

lemma inverse_formula (Q Q₀ R₀ : Matrix S S D) (hQR : Q₀*R₀=1) (hRQ : R₀*Q₀=1)
    (n : ℕ) (hN : (R₀*(Q-Q₀))^n=0) : Q⁻¹=series (R₀*(Q-Q₀)) n*R₀ := by
  let N := R₀*(Q-Q₀)
  have hfac : Q=Q₀*(1+N) := by
    dsimp [N]
    rw [mul_add,mul_one,← mul_assoc,hQR,one_mul]
    abel
  apply Matrix.inv_eq_left_inv
  calc
    _ = series N n*(R₀*Q) := mul_assoc _ _ _
    _ = series N n*(R₀*(Q₀*(1+N))) := by rw [hfac]
    _ = series N n*(1+N) := by rw [← mul_assoc R₀ Q₀ (1+N),hRQ,one_mul]
    _ = 1 := series_mul N n hN
end
end OddKaplansky.FiniteMatrixInverse

end

end OAI
