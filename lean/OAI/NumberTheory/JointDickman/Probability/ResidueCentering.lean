import OAI.NumberTheory.JointDickman.Probability.FiniteChannels

namespace OAI

/-!
# Centering finite channels in the residue coordinate

All residues above the same base cell carry the same atom weight. Thus
subtracting the residue average of the transition subtracts exactly the
residue average of the channel. The corresponding two-split kernel is
centered in both coordinates. A residue-independent approximation cancels,
at a loss of at most four in its uniform error.
-/

namespace JointDickman

open scoped BigOperators

noncomputable def finiteResidueAverage {R : Type*} [Fintype R] (f : R → ℝ) : ℝ :=
  (∑ r, f r) / Fintype.card R

theorem finiteResidueAverage_add {R : Type*} [Fintype R] (f g : R → ℝ) :
    finiteResidueAverage (fun r => f r + g r) =
      finiteResidueAverage f + finiteResidueAverage g := by
  simp [finiteResidueAverage, Finset.sum_add_distrib, add_div]

theorem finiteResidueAverage_sub {R : Type*} [Fintype R] (f g : R → ℝ) :
    finiteResidueAverage (fun r => f r - g r) =
      finiteResidueAverage f - finiteResidueAverage g := by
  simp [finiteResidueAverage, Finset.sum_sub_distrib, sub_div]

theorem finiteResidueAverage_mul_const {R : Type*} [Fintype R] (f : R → ℝ) (c : ℝ) :
    finiteResidueAverage (fun r => f r * c) = finiteResidueAverage f * c := by
  simp only [finiteResidueAverage, ← Finset.sum_mul]
  ring

theorem finiteResidueAverage_const_mul {R : Type*} [Fintype R] (f : R → ℝ) (c : ℝ) :
    finiteResidueAverage (fun r => c * f r) = c * finiteResidueAverage f := by
  simp only [finiteResidueAverage, ← Finset.mul_sum]
  ring

theorem finiteResidueAverage_div_const {R : Type*} [Fintype R] (f : R → ℝ) (c : ℝ) :
    finiteResidueAverage (fun r => f r / c) = finiteResidueAverage f / c := by
  simp only [finiteResidueAverage, ← Finset.sum_div]
  ring

theorem finiteResidueAverage_sum {S R : Type*} [Fintype S] [Fintype R] (f : S → R → ℝ) :
    finiteResidueAverage (fun r => ∑ s, f s r) = ∑ s, finiteResidueAverage (f s) := by
  unfold finiteResidueAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteResidueAverage_const {R : Type*} [Fintype R] [Nonempty R] (c : ℝ) :
    finiteResidueAverage (fun _ : R => c) = c := by
  have hn : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteResidueAverage, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hn

theorem finiteResidueAverage_abs_le {R : Type*} [Fintype R] [Nonempty R]
    (f : R → ℝ) {ε : ℝ} (hf : ∀ r, |f r| ≤ ε) : |finiteResidueAverage f| ≤ ε := by
  have hn : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  calc
    |finiteResidueAverage f| = |∑ r, f r| / (Fintype.card R : ℝ) := by
      simp only [finiteResidueAverage, abs_div, abs_of_pos hn]
    _ ≤ (∑ r, |f r|) / (Fintype.card R : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn.le
    _ ≤ (∑ _r : R, ε) / (Fintype.card R : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun r _ => hf r)) hn.le
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel_left₀ ε hn.ne'

/-- Subtract the uniform residue average within each base cell. -/
noncomputable def residueCenteredTransition {Ω D R : Type*} [Fintype R]
    (p : Ω → D × R → ℝ) (s : Ω) (a : D × R) : ℝ :=
  p s a - finiteResidueAverage (fun t => p s (a.1, t))

theorem residueCenteredTransition_average {Ω D R : Type*} [Fintype R] [Nonempty R]
    (p : Ω → D × R → ℝ) (s : Ω) (d : D) :
    finiteResidueAverage (fun r => residueCenteredTransition p s (d, r)) = 0 := by
  unfold residueCenteredTransition
  change finiteResidueAverage (fun r => p s (d, r) -
    finiteResidueAverage (fun t => p s (d, t))) = 0
  rw [finiteResidueAverage_sub, finiteResidueAverage_const, sub_self]

/-- Equal cell weights make transition centering exactly channel centering.
The identity also holds at zero weights, under the usual totalized division. -/
theorem finiteChannel_residueCentered {Ω D R : Type*} [Fintype Ω] [Fintype D] [Fintype R]
    (w : Ω → ℝ) (μ : D → ℝ) (p : Ω → D × R → ℝ) (f : Ω → ℝ) (d : D) (r : R) :
    finiteChannel w (fun a : D × R => μ a.1) (residueCenteredTransition p) f (d, r) =
      finiteChannel w (fun a : D × R => μ a.1) p f (d, r) -
        finiteResidueAverage (fun t => finiteChannel w (fun a : D × R => μ a.1) p f (d, t)) := by
  have hp (s : Ω) : w s * residueCenteredTransition p s (d, r) * f s =
      w s * p s (d, r) * f s - finiteResidueAverage (fun t => w s * p s (d, t) * f s) := by
    rw [finiteResidueAverage_mul_const, finiteResidueAverage_const_mul]
    unfold residueCenteredTransition
    ring
  unfold finiteChannel
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, sub_div, finiteResidueAverage_div_const, finiteResidueAverage_sum]

/-- Center a kernel in both of its residue coordinates. -/
noncomputable def residueCenteredKernel {D R : Type*} [Fintype R]
    (K : D × R → D × R → ℝ) (a b : D × R) : ℝ :=
  K a b - finiteResidueAverage (fun t => K (a.1, t) b) -
    finiteResidueAverage (fun u => K a (b.1, u)) +
      finiteResidueAverage (fun t => finiteResidueAverage (fun u => K (a.1, t) (b.1, u)))

/-- The kernel of the centered channel is the actual four-term centered
two-split kernel. No nonzero-weight assumption is needed for this identity. -/
theorem finiteTwoSplitKernel_residueCentered {Ω D R : Type*}
    [Fintype Ω] [Fintype R] (w : Ω → ℝ) (μ : D → ℝ) (p : Ω → D × R → ℝ)
    (d e : D) (r s : R) :
    finiteTwoSplitKernel w (fun a : D × R => μ a.1) (residueCenteredTransition p) (d, r) (e, s) =
      residueCenteredKernel (finiteTwoSplitKernel w (fun a : D × R => μ a.1) p) (d, r) (e, s) := by
  have hp (x : Ω) : w x * residueCenteredTransition p x (d, r) *
      residueCenteredTransition p x (e, s) =
      w x * p x (d, r) * p x (e, s) -
        finiteResidueAverage (fun t => w x * p x (d, t) * p x (e, s)) -
        finiteResidueAverage (fun u => w x * p x (d, r) * p x (e, u)) +
        finiteResidueAverage (fun t => finiteResidueAverage (fun u => w x * p x (d, t) * p x (e, u))) := by
    simp only [finiteResidueAverage_mul_const, finiteResidueAverage_const_mul]
    unfold residueCenteredTransition
    ring
  unfold finiteTwoSplitKernel residueCenteredKernel
  simp_rw [hp, finiteResidueAverage_div_const, finiteResidueAverage_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, add_div, sub_div]

theorem residueCenteredKernel_sub_base {D R : Type*} [Fintype R] [Nonempty R]
    (K : D × R → D × R → ℝ) (G : D → D → ℝ) (d e : D) (r s : R) :
    residueCenteredKernel K (d, r) (e, s) =
      residueCenteredKernel (fun a b => K a b - G a.1 b.1) (d, r) (e, s) := by
  unfold residueCenteredKernel
  simp_rw [finiteResidueAverage_sub, finiteResidueAverage_const]
  ring

/-- A residue-independent approximating kernel disappears after centering;
the four remaining averages each contribute at most the uniform error. -/
theorem residueCenteredKernel_abs_le {D R : Type*} [Fintype R] [Nonempty R]
    (K : D × R → D × R → ℝ) (G : D → D → ℝ) {ε : ℝ}
    (hK : ∀ d e r s, |K (d, r) (e, s) - G d e| ≤ ε) (d e : D) (r s : R) :
    |residueCenteredKernel K (d, r) (e, s)| ≤ 4 * ε := by
  rw [residueCenteredKernel_sub_base K G]
  unfold residueCenteredKernel
  have h₀ := hK d e r s
  have h₁ := finiteResidueAverage_abs_le (fun t => K (d, t) (e, s) - G d e)
    (fun t => hK d e t s)
  have h₂ := finiteResidueAverage_abs_le (fun u => K (d, r) (e, u) - G d e)
    (fun u => hK d e r u)
  have h₃ := finiteResidueAverage_abs_le
    (fun t => finiteResidueAverage (fun u => K (d, t) (e, u) - G d e))
    (fun t => finiteResidueAverage_abs_le _ (fun u => hK d e t u))
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h₀ h₁)) h₂)) h₃).trans
      (by ring_nf; exact le_rfl))

/-- Application of the uniform centering bound to the actual centered
two-split kernel of the transition. -/
theorem finiteTwoSplitKernel_centered_abs_le {Ω D R : Type*}
    [Fintype Ω] [Fintype R] [Nonempty R]
    (w : Ω → ℝ) (μ : D → ℝ) (p : Ω → D × R → ℝ) (G : D → D → ℝ) {ε : ℝ}
    (hK : ∀ d e r s,
      |finiteTwoSplitKernel w (fun a : D × R => μ a.1) p (d, r) (e, s) - G d e| ≤ ε)
    (d e : D) (r s : R) :
    |finiteTwoSplitKernel w (fun a : D × R => μ a.1) (residueCenteredTransition p)
      (d, r) (e, s)| ≤ 4 * ε := by
  rw [finiteTwoSplitKernel_residueCentered]
  exact residueCenteredKernel_abs_le _ G hK d e r s

end JointDickman

end OAI
