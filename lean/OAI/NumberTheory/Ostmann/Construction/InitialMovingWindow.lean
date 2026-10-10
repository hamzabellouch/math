import OAI.NumberTheory.Ostmann.Construction.InitialMovingPrior
import OAI.NumberTheory.Ostmann.Construction.SelectedInitialProductWindow

namespace OAI

/-! # The selected full-prior window after fixing the spectators -/
namespace Ostmann
open scoped Classical BigOperators

private theorem primeSubsetPrior_ne_zero (P Q : Finset ℕ) (p : P)
    (hp : (p : ℕ).Prime) (hmem : (p : ℕ) ∈ Q) : primeSubsetPrior P Q p ≠ 0 := by
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.pos)
  have hm : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹ :=
    Finset.sum_pos' (fun _ _ => by positivity) ⟨p, hmem, hpos⟩
  simp only [primeSubsetPrior, ite_eq_left hmem]
  exact ne_of_gt (div_pos hpos hm)

theorem selected_initial_moving_window
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D Qd : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) centers targets)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (b d : ℕ)
    (μb : Fin b → P → ℝ) (sl sr : Fin d → P)
    (hsl : ∀ i, (sl i : ℕ) ∈ Qd) (hsr : ∀ i, (sr i : ℕ) ∈ Qd) :
    let cells := initialSmallCellList top centers
    let μg := smoothGiantPrior P logCellProfile G
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y endpoint D (cells.get i))
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    ∀ (XL XR : P) (y : MovingRegularSlot 0 (cells.length + cells.length) (b + b) → P),
      μg XL ≠ 0 → μg XR ≠ 0 →
      (∏ i, initialMovingRegularPrior b cells.length μb μc i (y i)) ≠ 0 →
      initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d cells.length cb cd sl sr y ≠ 0 →
      ((∏ i, ((initialMovingTuple b d cells.length sl sr XL XR y i : P) : ℕ) : ℕ) : ℝ) /
        Real.exp Y ∈ Set.Icc (Real.exp (Δ - 2 * (cells.length + 3)))
          (Real.exp (Δ + 2 * (cells.length + 3))) := by
  intro cells μg μc Δ XL XR y hXL hXR hy hw
  have hs (i : Fin d) : primeSubsetPrior P Qd (sl i) ≠ 0 := by
    exact primeSubsetPrior_ne_zero P Qd (sl i) (hP _ (sl i).property) (hsl i)
  have ht (i : Fin d) : primeSubsetPrior P Qd (sr i) ≠ 0 := by
    exact primeSubsetPrior_ne_zero P Qd (sr i) (hP _ (sr i).property) (hsr i)
  have hp := initialMovingTuple_prior_nonzero b d cells.length μg μb
    (fun _ => primeSubsetPrior P Qd) μc sl sr hs ht XL XR hXL hXR y hy
  have hc : doubledHalfWeight (fun z : Fin (b + (d + cells.length) + 1) → P =>
      (initialHalfCutoffWeight (fun p : P => (p : ℕ)) b d cells.length cb cd (Fin.tail z) : ℂ))
      (initialMovingTuple b d cells.length sl sr XL XR y) ≠ 0 := by
    rwa [initialMovingTuple_cutoff]
  have h := selected_initial_product_window htop hcenters P hP b d μb
    (fun _ => primeSubsetPrior P Qd) (initialMovingTuple b d cells.length sl sr XL XR y) hp hc
  have he : ((∏ i, ((initialMovingTuple b d cells.length sl sr XL XR y i : P) : ℕ) : ℕ) : ℝ) =
      ∏ i, (((initialMovingTuple b d cells.length sl sr XL XR y i : P) : ℕ) : ℝ) := by
    push_cast
    rfl
  rw [he]
  exact ⟨(le_div_iff₀ (Real.exp_pos Y)).mpr (by simpa only [mul_comm] using h.1),
    (div_le_iff₀ (Real.exp_pos Y)).mpr (by simpa only [mul_comm] using h.2)⟩

end Ostmann

end OAI
