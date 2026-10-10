import OAI.NumberTheory.Ostmann.Characters.PeriodicCancellation

namespace OAI

open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters

theorem sum_residue_representatives {M : ℕ} [NeZero M] (f : ZMod M → ℂ) :
    ∑ n ∈ Finset.range M, f n = ∑ z : ZMod M, f z := by
  rw [← Fin.sum_univ_eq_sum_range (fun n : ℕ => f n) M]
  apply Fintype.sum_equiv (ZMod.finEquiv M).toEquiv _ f
  intro i
  congr 1
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M => exact ZMod.natCast_zmod_val (n := M+1) i

theorem norm_crtProduct_le_one {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (h : q.Coprime q') (χ : MulChar (ZMod q) ℂ) (ξ : MulChar (ZMod q') ℂ)
    (n : ZMod (q*q')) : ‖crtProduct h χ ξ n‖ ≤ 1 := by
  rw [crtProduct, norm_mul, Complex.norm_conj]
  simpa using mul_le_mul (norm_character_le_one χ _) (norm_character_le_one ξ _)
    (norm_nonneg _) (by norm_num : (0:ℝ)≤1)

theorem norm_crtProduct_sum_range_le {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (h : q.Coprime q') (χ : MulChar (ZMod q) ℂ) (ξ : MulChar (ZMod q') ℂ)
    (hχ : χ ≠ 1) (u : (ZMod (q*q'))ˣ) (a : ZMod (q*q')) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, crtProduct h χ ξ (↑u*(n:ZMod (q*q'))+a)‖ ≤ (q*q' : ℕ) := by
  apply norm_periodic_sum_le (M := q*q')
  · exact Nat.mul_pos (NeZero.pos q) (NeZero.pos q')
  · intro n
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero]
  · rw [sum_residue_representatives (fun z : ZMod (q*q') => crtProduct h χ ξ (↑u*z+a))]
    exact crtProduct_sum_affine_zero h χ ξ hχ u a
  · intro n
    exact norm_crtProduct_le_one h χ ξ _

theorem norm_crtProduct_weighted_sum_le {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (h : q.Coprime q') (χ : MulChar (ZMod q) ℂ) (ξ : MulChar (ZMod q') ℂ)
    (hχ : χ ≠ 1) (u : (ZMod (q*q'))ˣ) (a : ZMod (q*q')) (w : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n * crtProduct h χ ξ (↑u*(n:ZMod (q*q'))+a)‖ ≤
      (q*q' : ℕ) * (‖w (N-1)‖ + ∑ n ∈ Finset.range (N-1), ‖w (n+1)-w n‖) := by
  apply norm_weighted_sum_le (by positivity)
  exact fun n => norm_crtProduct_sum_range_le h χ ξ hχ u a n
end Ostmann.Characters

end OAI
