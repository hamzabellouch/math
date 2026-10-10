import OAI.Analysis.CircleDomains.Transfer.RealGridTransfer
import OAI.Analysis.CircleDomains.Modulus.TerminalOscillation

namespace OAI

/-!
# Actual terminal oscillations after smooth filling

The fillings leave terminal boundaries unchanged. Since these boundaries
lie in the one-plateau of the cutoff, their transferred coordinates are
exactly the selected staircases. The original pointwise oscillation bound
therefore gives the required square-sum bound for the actual boundary
diameters, rather than for separately supplied numbers.
-/

open Set Filter Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def terminalOscillation (T : ℂ ≃ₜ ℂ) (f : (ℝ × ℝ) → ℝ) : ℝ :=
  Metric.diam (f '' frontier (realJordanInterior T))

theorem filled_eq_staircase_on_terminal
    {I J : Type*} {n : ℕ} (T : I → ℂ ≃ₜ ℂ) (H : J → ℂ ≃ₜ ℂ)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    {Ω : Set (ℝ × ℝ)} (u : Fin n → (ℝ × ℝ) → ℝ) (χ : (ℝ × ℝ) → ℝ)
    {h δ : ℝ} (θ : Fin n → ℝ) {F : Fin n → (ℝ × ℝ) → ℝ}
    (hF : IsFilledCoordinateFamily (fun j => realJordanInterior (H j)) Ω
      (cutoffCoordinateFamily u χ h δ θ) F)
    (hTC : ∀ i, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (T i))) (cutoffCore χ))
    (i : I) (l : Fin n) {z : ℂ} (hz : z ∈ frontier (jordanInterior (T i))) :
    F l (Complex.equivRealProdCLM z) = shiftedStaircase h δ (θ l) (u l (Complex.equivRealProdCLM z)) := by
  have hnot (j : J) : Complex.equivRealProdCLM z ∉ realJordanInterior (H j) := by
    rintro ⟨w, hw, heq⟩
    have hwz : w = z := Complex.equivRealProdCLM.injective heq
    exact Set.disjoint_left.mp (hTH i j) (frontier_subset_closure hz)
      (hwz ▸ subset_closure hw)
  have hχ : χ (Complex.equivRealProdCLM z) = 1 :=
    (interior_subset : interior {x | χ x = 1} ⊆ {x | χ x = 1})
      (boundary_in_one_plateau_of_disjoint_cutoffCore (T i) χ (hTC i) z hz)
  exact (hF.2.1 l _ hnot).trans (cutoffStaircase_of_one hχ)

theorem terminalOscillation_le_of_staircase_bound
    {I J : Type*} {n : ℕ} (T : I → ℂ ≃ₜ ℂ) (H : J → ℂ ≃ₜ ℂ)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    {Ω : Set (ℝ × ℝ)} (u : Fin n → (ℝ × ℝ) → ℝ) (χ : (ℝ × ℝ) → ℝ)
    {h δ : ℝ} (hh : 0 ≤ h) (θ : Fin n → ℝ) {F : Fin n → (ℝ × ℝ) → ℝ}
    (hF : IsFilledCoordinateFamily (fun j => realJordanInterior (H j)) Ω
      (cutoffCoordinateFamily u χ h δ θ) F)
    (hTC : ∀ i, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (T i))) (cutoffCore χ))
    (a : I → Fin n → ℝ) (ha : ∀ i l, 0 ≤ a i l)
    (hbound : ∀ i l x, x ∈ frontier (jordanInterior (T i)) →
      ∀ y ∈ frontier (jordanInterior (T i)),
        |shiftedStaircase h δ (θ l) (u l (Complex.equivRealProdCLM x)) -
          shiftedStaircase h δ (θ l) (u l (Complex.equivRealProdCLM y))| ≤ a i l + 4 * h) :
    ∀ i l, terminalOscillation (T i) (F l) ≤ a i l + 4 * h := by
  intro i l
  apply Metric.diam_le_of_forall_dist_le (by linarith [ha i l])
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
  rw [frontier_realJordanInterior] at hp hq
  obtain ⟨z, hz, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hq
  rw [filled_eq_staircase_on_terminal T H hTH u χ θ hF hTC i l hz,
    filled_eq_staircase_on_terminal T H hTH u χ θ hF hTC i l hw]
  simpa only [Real.dist_eq] using hbound i l z hz w hw

/-- The selected terminal-count bound controls the actual square-sum of
excess boundary oscillations for every transferred coordinate. -/
theorem transferred_terminal_oscillation_bound
    {I J : Type*} [Fintype I] {n : ℕ} (T : I → ℂ ≃ₜ ℂ) (H : J → ℂ ≃ₜ ℂ)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    {Ω : Set (ℝ × ℝ)} (u : Fin n → (ℝ × ℝ) → ℝ) (χ : (ℝ × ℝ) → ℝ)
    {h δ η : ℝ} (hh : 0 ≤ h) (θ : Fin n → ℝ) {F : Fin n → (ℝ × ℝ) → ℝ}
    (hF : IsFilledCoordinateFamily (fun j => realJordanInterior (H j)) Ω
      (cutoffCoordinateFamily u χ h δ θ) F)
    (hTC : ∀ i, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (T i))) (cutoffCore χ))
    (a : I → Fin n → ℝ) (ha : ∀ i l, 0 ≤ a i l)
    (hbound : ∀ i l x, x ∈ frontier (jordanInterior (T i)) →
      ∀ y ∈ frontier (jordanInterior (T i)),
        |shiftedStaircase h δ (θ l) (u l (Complex.equivRealProdCLM x)) -
          shiftedStaircase h δ (θ l) (u l (Complex.equivRealProdCLM y))| ≤ a i l + 4 * h)
    (hsmall : h * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∀ l, Real.sqrt (∑ i : I, max (terminalOscillation (T i) (F l) - a i l) 0 ^ 2) < 4 * η := by
  intro l
  have hosc := terminalOscillation_le_of_staircase_bound T H hTH u χ hh θ hF hTC a ha hbound
  simpa only [Finset.card_univ] using
    sqrt_sum_terminal_excess_sq_lt Finset.univ Finset.univ (Subset.refl _)
      (fun i => terminalOscillation (T i) (F l)) (fun i => a i l) hh
      (fun i _ => hosc i l) (by simpa only [Finset.card_univ] using hsmall)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
