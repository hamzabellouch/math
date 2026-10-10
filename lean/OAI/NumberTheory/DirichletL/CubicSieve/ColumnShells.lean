import OAI.NumberTheory.DirichletL.CubicSieve.QuotientColumns

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve FiniteSieveRestriction
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicColumnLabel {n : Type*} (cols : n → Ideal O) (N : ℝ) (j : n) :
    Fin (columnDyadicLength N + 1) := divisorDyadicLabel N (cols j)

abbrev CubicColumnShell {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (l : Fin (columnDyadicLength N + 1)) := {j : n // cubicColumnLabel cols N j = l}

lemma cubicColumnShell_bounds {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (hc : ∀ j, Admissible (cols j)) (hn : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (l : Fin (columnDyadicLength N + 1)) (j : CubicColumnShell cols N l) :
    (2 : ℝ)^l.val/2 ≤ (Ideal.absNorm (cols j.val) : ℝ) ∧
      (Ideal.absNorm (cols j.val) : ℝ) ≤ (2 : ℝ)^l.val := by
  have hp : 1 ≤ (Ideal.absNorm (cols j.val) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (primaryGenerator_ne_zero_ideal _ (hc j.val).2))
  have hb := divisorDyadicLabel_bounds N (cols j.val) hp (hn j.val)
  have hj := j.property
  change divisorDyadicLabel N (cols j.val) = l at hj
  rw [hj] at hb
  exact ⟨hb.1.le,hb.2⟩

lemma cubicColumnShell_scale_le {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (hc : ∀ j, Admissible (cols j)) (hn : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (l : Fin (columnDyadicLength N + 1)) (j : CubicColumnShell cols N l) :
    (2 : ℝ)^l.val ≤ 2*N := by
  have hh := (cubicColumnShell_bounds cols N hc hn l j).1
  linarith [hn j.val]

lemma cubicColumnShell_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (N : ℝ) (a : n → ℂ) :
    (∑ l : Fin (columnDyadicLength N + 1), ∑ j : CubicColumnShell cols N l, ‖a j.val‖^2) =
      ∑ j, ‖a j‖^2 := Fintype.sum_fiberwise (cubicColumnLabel cols N) (fun j => ‖a j‖^2)

theorem cubic_energy_column_shells {n : Type*} [Fintype n]
    (cols : n → Ideal O) (N : ℝ) (a : n → ℂ) (R : Finset O) :
    (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
      (columnDyadicLength N + 1 : ℝ) *
        ∑ l : Fin (columnDyadicLength N + 1), ∑ z ∈ R,
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z * a j.val‖^2 := by
  have hp (z : O) : ‖∑ j, cubicRow (cols j) z*a j‖^2 ≤
      (columnDyadicLength N + 1 : ℝ)*∑ l : Fin (columnDyadicLength N + 1),
        ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2 := by
    rw [← Fintype.sum_fiberwise (cubicColumnLabel cols N) (fun j => cubicRow (cols j) z*a j)]
    calc
      _ ≤ (∑ l : Fin (columnDyadicLength N + 1),
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
          (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ))
            (fun l : Fin (columnDyadicLength N + 1) =>
              ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖))
  calc
    _ ≤ ∑ z ∈ R, (columnDyadicLength N + 1 : ℝ)*
        ∑ l : Fin (columnDyadicLength N + 1),
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2 :=
      Finset.sum_le_sum (fun z hz => hp z)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end
end SevenEighths.CubicSieve

end OAI
