import OAI.NumberTheory.Ostmann.QuadraticSieveNorm

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def supportCoefficients (S : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact if n ∈ S then a n else 0

@[simp] theorem supportCoefficients_apply_mem (S : Finset ℕ) (a : ℕ → ℂ)
    {n : ℕ} (hn : n ∈ S) : supportCoefficients S a n = a n := by
  classical
  simp [supportCoefficients, hn]

@[simp] theorem supportCoefficients_apply_not_mem (S : Finset ℕ) (a : ℕ → ℂ)
    {n : ℕ} (hn : n ∉ S) : supportCoefficients S a n = 0 := by
  classical
  simp [supportCoefficients, hn]

theorem jacobi_sum_supportCoefficients {S T : Finset ℕ} (hST : S ⊆ T)
    (a : ℕ → ℂ) (v : ℕ) :
    (∑ n ∈ T, supportCoefficients S a n * (jacobiSym (n : ℤ) v : ℂ)) =
      ∑ n ∈ S, a n * (jacobiSym (n : ℤ) v : ℂ) := by
  classical
  calc
    _ = ∑ n ∈ S, supportCoefficients S a n * (jacobiSym (n : ℤ) v : ℂ) := by
      symm
      apply Finset.sum_subset hST
      intro n hn hnot
      simp [hnot]
    _ = _ := Finset.sum_congr rfl (fun n hn => by simp [hn])

theorem coefficientEnergy_supportCoefficients {S T : Finset ℕ} (hST : S ⊆ T)
    (a : ℕ → ℂ) : coefficientEnergy T (supportCoefficients S a) = coefficientEnergy S a := by
  classical
  unfold coefficientEnergy
  calc
    _ = ∑ n ∈ S, ‖supportCoefficients S a n‖ ^ 2 := by
      symm
      apply Finset.sum_subset hST
      intro n hn hnot
      simp [hnot]
    _ = _ := Finset.sum_congr rfl (fun n hn => by simp [hn])

theorem jacobiEnergy_supportCoefficients (V : Finset ℕ) {S T : Finset ℕ}
    (hST : S ⊆ T) (a : ℕ → ℂ) :
    jacobiEnergy V T (supportCoefficients S a) = jacobiEnergy V S a := by
  unfold jacobiEnergy
  simp_rw [jacobi_sum_supportCoefficients hST]

theorem quadraticNorm_mono_columns (V : Finset ℕ) {S T : Finset ℕ} (hST : S ⊆ T) :
    quadraticNorm V S ≤ quadraticNorm V T := by
  apply quadraticNorm_le_of_bound V S (quadraticNorm_nonneg V T)
  intro a
  simpa only [jacobiEnergy_supportCoefficients V hST,
    coefficientEnergy_supportCoefficients hST] using
    jacobiEnergy_le_quadraticNorm V T (supportCoefficients S a)

theorem quadraticNorm_mono {V W S T : Finset ℕ} (hVW : V ⊆ W) (hST : S ⊆ T) :
    quadraticNorm V S ≤ quadraticNorm W T :=
  (quadraticNorm_mono_rows hVW S).trans (quadraticNorm_mono_columns W hST)

end Ostmann.QuadraticSieve

end OAI
