import OAI.NumberTheory.Ostmann.Preliminaries.MoebiusSquareRemoval

namespace OAI

/-! # The finite rectangular expansion underlying the original coefficients -/

namespace Ostmann

open scoped BigOperators

noncomputable def squarefreeKernelSupport (L N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun s => Squarefree s ∧ s.Coprime L)

theorem mem_squarefreeKernelSupport (L N s : ℕ) :
    s ∈ squarefreeKernelSupport L N ↔ 1 ≤ s ∧ s ≤ N ∧ Squarefree s ∧ s.Coprime L := by
  simp only [squarefreeKernelSupport, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem frequencyTriples_rectangle (L N : ℕ) (hL : Squarefree L) :
    frequencyTriples L N =
      ((squarefreeKernelSupport L N).product (L.divisors.product (Finset.Icc 1 N))).filter
        (fun z => z.1 * z.2.1 * z.2.2 ^ 2 ≤ N) := by
  classical
  ext z
  rcases z with ⟨s, v, w⟩
  simp only [mem_frequencyTriples, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc, mem_squarefreeKernelSupport]
  constructor
  · rintro ⟨hs, hsN, hv, hw, hwN, hsv, hcop, hval⟩
    exact ⟨⟨⟨hs, hsN, hsv.of_mul_left, hcop⟩, hv, hw, hwN⟩, hval⟩
  · rintro ⟨⟨⟨hs, hsN, hsf, hcop⟩, hv, hw, hwN⟩, hval⟩
    have hvd := (Nat.mem_divisors.mp hv).1
    have hvf : Squarefree v := hL.squarefree_of_dvd hvd
    have hsv : Squarefree (s * v) := squarefree_mul_iff.mpr
      ⟨Nat.coprime_iff_isRelPrime.mp (hcop.of_dvd_right hvd), hsf, hvf⟩
    exact ⟨hs, hsN, hv, hw, hwN, hsv, hcop, hval⟩

theorem sum_frequencyTriples_rectangle (L N : ℕ) (hL : Squarefree L)
    (F : ℕ × ℕ × ℕ → ℂ)
    (hF : ∀ z, N < z.1 * z.2.1 * z.2.2 ^ 2 → F z = 0) :
    (∑ z ∈ frequencyTriples L N, F z) =
      ∑ s ∈ squarefreeKernelSupport L N, ∑ v ∈ L.divisors, ∑ w ∈ Finset.Icc 1 N, F (s, v, w) := by
  classical
  rw [frequencyTriples_rectangle L N hL]
  calc
    _ = ∑ z ∈ (squarefreeKernelSupport L N).product (L.divisors.product (Finset.Icc 1 N)), F z := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro z hz hn
      apply hF
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hz, by omega⟩)
    _ = _ := by simp only [Finset.product_eq_sprod, Finset.sum_product]

/-- Inclusion-exclusion and unique squarefree decomposition give
the three nested sums defining C_s^(P), with a common finite support. -/
theorem rectangular_frequency_moebius_expansion (L N : ℕ) (hL : Squarefree L)
    {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) (hχ : χ.IsQuadratic)
    (F : ℕ → ℂ) (hF : ∀ u, N < u → F u = 0) :
    (∑ u ∈ Finset.Icc 1 N, χ (u : ZMod M) * F u) =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ s ∈ squarefreeKernelSupport L N, χ (s : ZMod M) *
          ∑ v ∈ L.divisors, χ (v : ZMod M) *
            ∑ w ∈ (Finset.Icc 1 N).filter (fun w => P ∣ w), F (s * v * w ^ 2) := by
  classical
  rw [squarefree_frequency_moebius_expansion L N (Nat.pos_of_ne_zero hL.ne_zero) hM χ hχ F]
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  rw [Finset.sum_filter]
  rw [sum_frequencyTriples_rectangle L N hL _ (by
    intro z hz
    simp only [hF _ hz, mul_zero, ite_self])]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> ring

end Ostmann

end OAI
