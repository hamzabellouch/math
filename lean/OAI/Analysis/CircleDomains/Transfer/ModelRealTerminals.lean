import OAI.Analysis.CircleDomains.Transfer.ModelRealSubfamily
import OAI.Analysis.CircleDomains.Transfer.TerminalTransfer

namespace OAI

/-! Actual boundary oscillation control for the preserved real barriers
of a mixed model. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {J I A : Type*} {n N : ℕ} {T : J → ℂ ≃ₜ ℂ} {H : I → ℂ ≃ₜ ℂ}
  {G K : Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
  {f : Fin n → (ℝ × ℝ) → UnitAddCircle} {χ : (ℝ × ℝ) → ℝ}
  {θ : Fin n → ℝ} {ε : ℝ} {Q : MaskedModelData T H G K M f χ N θ ε}
  {ι : A → Fin n} {r : A → (ℝ × ℝ) → ℝ}

theorem ModelRealSubfamily.terminal_value (W : ModelRealSubfamily Q ι r)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    (hTC : ∀ i, Disjoint (closedTerminalCap (T i)) (cutoffCore χ))
    (i : J) (j : A) {z : ℂ} (hz : z ∈ frontier (jordanInterior (T i))) :
    W.functions j (Complex.equivRealProdCLM z) =
      shiftedStaircase (reciprocalGridStep N)
        (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j))
        (r j (Complex.equivRealProdCLM z)) := by
  have hnot (k : I) : Complex.equivRealProdCLM z ∉ realJordanInterior (H k) := by
    rintro ⟨w, hw, heq⟩
    have hwz : w = z := Complex.equivRealProdCLM.injective heq
    exact Set.disjoint_left.mp (hTH i k) (frontier_subset_closure hz) (hwz ▸ subset_closure hw)
  have hχ : χ (Complex.equivRealProdCLM z) = 1 :=
    (interior_subset : interior {x | χ x = 1} ⊆ {x | χ x = 1})
      (boundary_in_one_plateau_of_disjoint_cutoffCore (T i) χ (hTC i) z hz)
  exact (W.filled.2.1 j _ hnot).trans (cutoffStaircase_of_one hχ)

theorem ModelRealSubfamily.terminal_oscillation (W : ModelRealSubfamily Q ι r)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    (hTC : ∀ i, Disjoint (closedTerminalCap (T i)) (cutoffCore χ))
    (a : J → A → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (hbound : ∀ i j x, x ∈ frontier (jordanInterior (T i)) →
      ∀ y ∈ frontier (jordanInterior (T i)),
        |shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j))
            (r j (Complex.equivRealProdCLM x)) -
          shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j))
            (r j (Complex.equivRealProdCLM y))| ≤ a i j + 4 * reciprocalGridStep N) :
    ∀ i j, terminalOscillation (T i) (W.functions j) ≤ a i j + 4 * reciprocalGridStep N := by
  intro i j
  apply Metric.diam_le_of_forall_dist_le (by linarith [ha i j, reciprocalGridStep_pos N])
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
  rw [frontier_realJordanInterior] at hp hq
  obtain ⟨z, hz, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hq
  rw [W.terminal_value hTH hTC i j hz, W.terminal_value hTH hTC i j hw]
  simpa only [Real.dist_eq] using hbound i j z hz w hw

end CircleDomainRigidity.FiniteTransfer

end

end OAI
