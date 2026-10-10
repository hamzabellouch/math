import OAI.Analysis.Laughlin.Operators.Energy
import OAI.Analysis.Laughlin.Pair.AffineKernel

namespace OAI

namespace Laughlin
open scoped BigOperators

def pairSlice {N Q : ℕ} (ψ : State N Q) (i j : Fin N) (a : Configuration N Q)
    (x y : Fin (Q+1)) : ℂ := ψ (Function.update (Function.update a i x) j y)

theorem pairSlice_antisymmetric {N Q : ℕ} (ψ : State N Q) (hψ : Antisymmetric ψ)
    (i j : Fin N) (hij : i ≠ j) (a : Configuration N Q) :
    ∀ x y, pairSlice ψ i j a y x = -pairSlice ψ i j a x y := by
  intro x y
  have h := hψ i j hij (Function.update (Function.update a i x) j y)
  have hs : (Function.update (Function.update a i x) j y) ∘ Equiv.swap i j =
      Function.update (Function.update a i y) j x := by
    funext k
    by_cases hki : k = i
    · subst k; simp [hij]
    · by_cases hkj : k = j
      · subst k; simp [hij]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj,hki,hkj]
  simpa only [hs,pairSlice] using h

theorem pairSlice_anchor {N Q : ℕ} (ψ : State N Q) (i j : Fin N)
    (a : Configuration N Q) :
    pairSlice ψ i j (Function.update (Function.update a i 0) j 0) = pairSlice ψ i j a := by
  funext x y
  unfold pairSlice
  congr 1
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all

theorem energy_eq_zero_iff_pair_slices {N Q : ℕ} (ψ : State N Q) :
    energy ψ = 0 ↔ ∀ (i j : Fin N), i < j → ∀ a : Configuration N Q,
      ∀ p ∈ Finset.range (2*Q-1),
        (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*pairSlice ψ i j a x y) = 0 := by
  rw [energy_eq_zero_iff]
  constructor
  · intro h i j hij a p hp
    have h0 := h i j hij p (Finset.mem_range.mp hp)
      (Function.update (Function.update a i 0) j 0)
      (by simp [ne_of_lt hij]) (by simp)
    change (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*
      pairSlice ψ i j (Function.update (Function.update a i 0) j 0) x y) = 0 at h0
    simpa only [pairSlice_anchor] using h0
  · intro h i j hij p hp a hai haj
    exact h i j hij a p (Finset.mem_range.mpr hp)

theorem energy_eq_zero_iff_affine_pair_cubes {N Q : ℕ} (hQ : 2 ≤ Q)
    (ψ : State N Q) (hψ : Antisymmetric ψ) :
    energy ψ = 0 ↔ ∀ (i j : Fin N), i < j → ∀ a : Configuration N Q,
      PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q (pairSlice ψ i j a) := by
  rw [energy_eq_zero_iff_pair_slices]
  constructor
  · intro h i j hij a
    exact (pair_kernel_iff_affine_cube Q hQ _
      (pairSlice_antisymmetric ψ hψ i j (ne_of_lt hij) a)).mp (h i j hij a)
  · intro h i j hij a
    exact (pair_kernel_iff_affine_cube Q hQ _
      (pairSlice_antisymmetric ψ hψ i j (ne_of_lt hij) a)).mpr (h i j hij a)

end Laughlin

end OAI
