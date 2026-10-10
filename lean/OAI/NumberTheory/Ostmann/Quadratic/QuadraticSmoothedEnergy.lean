import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveWeight
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernels
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdExpansion

namespace OAI

/-! # The literal smoothed odd moment and its large-kernel part -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticOddRange (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter Odd

noncomputable def quadraticRoughKernelRange (R K : ℕ) : Finset ℕ :=
  (quadraticOddRange R).filter (fun m => K < quadraticSquarefreePart m)

noncomputable def quadraticSmoothEnergy (M N : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ m ∈ quadraticOddRange (3 * M),
    quadraticSieveBump ((m : ℝ) / M) * ‖quadraticTransposeSum N b m‖ ^ 2

noncomputable def quadraticRoughEnergy (M N K : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ m ∈ quadraticRoughKernelRange (3 * M) K,
    quadraticSieveBump ((m : ℝ) / M) * ‖quadraticTransposeSum N b m‖ ^ 2

noncomputable def quadraticSmallEnergy (M N K : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ m ∈ quadraticSmallKernelRange (3 * M) K,
    quadraticSieveBump ((m : ℝ) / M) * ‖quadraticTransposeSum N b m‖ ^ 2

theorem quadratic_smooth_energy_split (M N K : ℕ) (b : ℕ → ℂ) :
    quadraticSmoothEnergy M N b =
      quadraticRoughEnergy M N K b + quadraticSmallEnergy M N K b := by
  have hs : (quadraticOddRange (3 * M)).filter
      (fun m => ¬ K < quadraticSquarefreePart m) = quadraticSmallKernelRange (3 * M) K := by
    ext m
    simp only [quadraticOddRange, quadraticSmallKernelRange, Finset.mem_filter, not_lt]
    tauto
  unfold quadraticSmoothEnergy quadraticRoughEnergy quadraticSmallEnergy quadraticRoughKernelRange
  rw [← hs]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem quadratic_rough_energy_nonneg (M N K : ℕ) (b : ℕ → ℂ) :
    0 ≤ quadraticRoughEnergy M N K b := by
  exact Finset.sum_nonneg (fun m _ => mul_nonneg (quadraticSieveBump_nonneg _) (sq_nonneg _))

theorem quadratic_rough_dyadic_domination {M N K : ℕ} (hM : 0 < M) (hK : K < M)
    (b : ℕ → ℂ) :
    (∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·),
      ‖quadraticTransposeSum N b m‖ ^ 2) ≤ quadraticRoughEnergy M N K b := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hw (m : ℕ) (hm : m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·)) :
      quadraticSieveBump ((m : ℝ) / M) = 1 := by
    obtain ⟨hm, hlo⟩ := Finset.mem_filter.mp hm
    have hhi := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    have hh := quadraticSieveWeight_eq_one (x := (m : ℝ) / M)
      (show (m : ℝ) / M ∈ Set.Icc 1 2 from ⟨
        (le_div_iff₀ hMR).mpr (by simpa only [one_mul] using (show (M : ℝ) ≤ m by exact_mod_cast hlo)),
        (div_le_iff₀ hMR).mpr (by exact_mod_cast hhi)⟩)
    rw [quadraticSieveWeight_apply] at hh
    exact_mod_cast hh
  calc
    _ = ∑ m ∈ (oddSquarefreeRange (2 * M)).filter (M ≤ ·),
        quadraticSieveBump ((m : ℝ) / M) * ‖quadraticTransposeSum N b m‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hw m hm, one_mul]
    _ ≤ quadraticRoughEnergy M N K b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨hm, hlo⟩ := Finset.mem_filter.mp hm
        obtain ⟨hi, ho, hsf⟩ := Finset.mem_filter.mp hm
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨?_, ho⟩, ?_⟩
        · apply Finset.mem_Icc.mpr
          obtain ⟨hl, hh⟩ := Finset.mem_Icc.mp hi
          omega
        · rw [(quadraticSquarefreePart_of_squarefree hsf).2]
          omega
      · intro m _ _
        exact mul_nonneg (quadraticSieveBump_nonneg _) (sq_nonneg _)

theorem quadratic_smooth_energy_gcd (M N : ℕ) (b : ℕ → ℂ) :
    (quadraticSmoothEnergy M N b : ℂ) =
      ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ quadraticOddRange (3 * M),
        quadraticSieveWeight ((m : ℝ) / M) *
          (if (m : ℤ).gcd d = 1 then (1 : ℂ) else 0) *
          quadraticGcdKernelSum N d b m := by
  unfold quadraticSmoothEnergy
  push_cast
  simp_rw [quadraticTranspose_norm_sq_gcd, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [quadraticSieveWeight_apply, mul_assoc]

end Ostmann

end OAI
