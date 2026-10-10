import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainPullback

namespace OAI

/-! # A finite parameterized gain chain as one product integral

This is the Fubini assembly used after replacing each physical collision by its
thermal and redundant-plane parameters. The transition maps and densities are
explicit functions, and the conclusion is an exact integral identity.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

def parameterChain (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞) (g : State → ℝ≥0∞)
    (i : ℕ) : ℕ → State → ℝ≥0∞
  | 0, z => g z
  | n+1, z => ∫⁻ p : StageControls, density i z p*
      parameterChain next density g (i+1) n (next i z p)

def chainIntegrand (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞) (g : State → ℝ≥0∞)
    (i : ℕ) : (n : ℕ) → State → (Fin n → StageControls) → ℝ≥0∞
  | 0, z, _ => g z
  | n+1, z, q => density i z (q 0)*
      chainIntegrand next density g (i+1) n (next i z (q 0)) (Fin.tail q)

theorem integrateControls_const_mul {c : ℝ≥0∞} (hc : c ≠ ∞) (n : ℕ)
    (F : (Fin n → StageControls) → ℝ≥0∞) :
    integrateControls n (fun q => c*F q) = c*integrateControls n F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [integrateControls,ih]
    exact lintegral_const_mul' _ _ hc

theorem parameterChain_eq_nested (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞)
    (hfinite : ∀ i z p, density i z p ≠ ∞) (g : State → ℝ≥0∞) (i n : ℕ) (z : State) :
    parameterChain next density g i n z =
      integrateControls n (chainIntegrand next density g i n z) := by
  induction n generalizing i z with
  | zero => rfl
  | succ n ih =>
    simp only [parameterChain,integrateControls]
    apply lintegral_congr
    intro p
    rw [ih]
    have he := integrateControls_const_mul (hfinite i z p) n
      (chainIntegrand next density g (i+1) n (next i z p))
    simpa only [chainIntegrand,Fin.cons_zero,Fin.tail_cons] using he.symm

theorem chainIntegrand_measurable (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞)
    (hnext : ∀ i, Measurable (fun p : State × StageControls => next i p.1 p.2))
    (hdensity : ∀ i, Measurable (fun p : State × StageControls => density i p.1 p.2))
    {g : State → ℝ≥0∞} (hg : Measurable g) (i n : ℕ) :
    Measurable (fun p : State × (Fin n → StageControls) =>
      chainIntegrand next density g i n p.1 p.2) := by
  induction n generalizing i with
  | zero => exact hg.comp measurable_fst
  | succ n ih =>
    have hfirst : Measurable (fun p : State × (Fin (n+1) → StageControls) => (p.1,p.2 0)) :=
      measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
    have htail : Measurable (fun p : State × (Fin (n+1) → StageControls) => Fin.tail p.2) := by
      exact Measurable.of_eval (fun j => (measurable_pi_apply j.succ).comp measurable_snd)
    exact ((hdensity i).comp hfirst).mul
      ((ih (i+1)).comp (((hnext i).comp hfirst).prodMk htail))

theorem parameterChain_eq_product (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞)
    (hnext : ∀ i, Measurable (fun p : State × StageControls => next i p.1 p.2))
    (hdensity : ∀ i, Measurable (fun p : State × StageControls => density i p.1 p.2))
    (hfinite : ∀ i z p, density i z p ≠ ∞) {g : State → ℝ≥0∞} (hg : Measurable g)
    (i n : ℕ) (z : State) :
    parameterChain next density g i n z =
      ∫⁻ q : Fin n → StageControls, chainIntegrand next density g i n z q := by
  rw [parameterChain_eq_nested next density hfinite g i n z]
  exact integrateControls_eq n ((chainIntegrand_measurable next density hnext hdensity hg i n).comp
    measurable_prodMk_left)

end BoltzmannNonuniqueness.FiveGainMap

end

end OAI
