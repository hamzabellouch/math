import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPriorBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedPrior
open Construction Preliminaries PrimeDyadicCover
open scoped BigOperators

theorem source_upper_of_log {A : ℕ} (E : Finset (PrimeUpTo A)) {β L : ℝ}
    (hmax : ∀p∈E,Real.log p.val≤Real.exp (β*L)) :
    ∀p∈E,p.val ≤ sourceUpper β L :=
  fun p hp=>le_sourceUpper_of_log (primeUpTo_prime p).pos (hmax p hp)

theorem source_cmean_eq_rows_of_log {A : ℕ} (Q : ℕ) (hQ : 0<Q)
    (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E) {β L : ℝ}
    (hmin : ∀p∈E,Q≤p.val) (hmax : ∀p∈E,Real.log p.val≤Real.exp (β*L))
    (f : PrimeUpTo A→ℂ) :
    (primeShellPrior E hE).cmean f=
      ∑i:Index (sourceUpper β L),
        ∑x:Fin Q × Fin (2*lower Q (sourceUpper β L) i+1),
          (sourceRowMass Q (sourceUpper β L) E i x:ℂ)*
            sourceTest f (rowValue Q (2*lower Q (sourceUpper β L) i+1) x) :=
  source_cmean_eq_rows_actual Q (sourceUpper β L) hQ E hE hmin (source_upper_of_log E hmax) f

theorem source_normalization_le {A : ℕ} (E : Finset (PrimeUpTo A)) {c L : ℝ}
    (hZ : Real.exp (-c*L)≤primeShellMass E) :
    1/primeShellMass E≤Real.exp (c*L) := by
  calc
    _ ≤ 1/Real.exp (-c*L) := one_div_le_one_div_of_le (Real.exp_pos _) hZ
    _ = _ := by rw [one_div,←Real.exp_neg]; congr 1; ring

theorem sourceTest_norm_le_one {A : ℕ} (f : PrimeUpTo A→ℂ)
    (hf : ∀p,‖f p‖≤1) (n : ℕ) : ‖sourceTest f n‖≤1 := by
  unfold sourceTest
  split_ifs with hn
  · exact hf _
  · simp

theorem source_cmean_norm_le_of_log {A : ℕ} (Q : ℕ) (hQ : 0<Q)
    (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E) {β L : ℝ}
    (hβ : 0≤β) (hL : 0≤L)
    (hmin : ∀p∈E,Q≤p.val) (hmax : ∀p∈E,Real.log p.val≤Real.exp (β*L))
    (f : PrimeUpTo A→ℂ) {B : ℝ} (hB : 0≤B)
    (hrows : ∀i:Index (sourceUpper β L),
      (block Q (sourceUpper β L) (sourceNaturals E) i).Nonempty →
      ‖∑x:Fin Q × Fin (2*lower Q (sourceUpper β L) i+1),
        (sourceRowMass Q (sourceUpper β L) E i x:ℂ)*
          sourceTest f (rowValue Q (2*lower Q (sourceUpper β L) i+1) x)‖≤B) :
    ‖(primeShellPrior E hE).cmean f‖≤(1/Real.log 2+1)*Real.exp (β*L)*B := by
  exact (source_cmean_norm_le_blocks Q (sourceUpper β L) hQ E hE hmin
    (source_upper_of_log E hmax) f hB hrows).trans
      (mul_le_mul_of_nonneg_right (card_le_exp hβ hL (log_sourceUpper_le β L)) hB)

end Ostmann.Characters.TemplateOneSidedPrior

end

end OAI
