import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowPicardSolution
import Mathlib.Analysis.ODE.ExistUnique

namespace OAI

/-! Global smooth dependence for a finite-dimensional autonomous flow.
The proof iterates the short-time implicit-function construction. -/

noncomputable section
namespace ForcedComputation.Flow
open Set
open scoped ContDiff NNReal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem flow_add {Z : E → E} {L : ℝ≥0} (hL : LipschitzWith L Z)
    {Ψ : ℝ → E → E}
    (hΨ : ∀ t x, HasDerivAt (fun s => Ψ s x) (Z (Ψ t x)) t)
    (hzero : ∀ x, Ψ 0 x = x) (s t : ℝ) (x : E) :
    Ψ (s + t) x = Ψ t (Ψ s x) := by
  have hd (r : ℝ) : HasDerivAt (fun u => Ψ (s + u) x)
      (Z (Ψ (s + r) x)) r := by
    simpa only [Function.comp_def, one_smul] using
      (hΨ (s + r) x).scomp r ((hasDerivAt_id r).const_add s)
  have he := ODE_solution_unique_univ (s := fun _ => univ)
    (fun _ => hL.lipschitzOnWith)
    (fun r => ⟨hd r, mem_univ _⟩)
    (fun r => ⟨hΨ r (Ψ s x), mem_univ _⟩)
    (show Ψ (s + 0) x = Ψ 0 (Ψ s x) by rw [add_zero, hzero])
  exact congrFun he t

def flowSteps (Ψ : ℝ → E → E) : ℕ → ℝ → E → E
  | 0, _, x => x
  | n + 1, τ, x => Ψ τ (flowSteps Ψ n τ x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem flowSteps_eq {Z : E → E} {L : ℝ≥0} (hL : LipschitzWith L Z)
    {Ψ : ℝ → E → E}
    (hΨ : ∀ t x, HasDerivAt (fun s => Ψ s x) (Z (Ψ t x)) t)
    (hzero : ∀ x, Ψ 0 x = x) (n : ℕ) (τ : ℝ) (x : E) :
    flowSteps Ψ n τ x = Ψ ((n : ℝ) * τ) x := by
  induction n with
  | zero => simp only [flowSteps, Nat.cast_zero, zero_mul, hzero]
  | succ n ih =>
    rw [flowSteps, ih, ← flow_add hL hΨ hzero]
    congr 2
    push_cast
    ring

theorem flowSteps_contDiffAt (Z : C(E, E))
    (hZ : ContDiff ℝ ∞ (Z : E → E)) {L : ℝ≥0} (hL : LipschitzWith L Z)
    {Ψ : ℝ → E → E}
    (hΨ : ∀ t x, HasDerivAt (fun s => Ψ s x) (Z (Ψ t x)) t)
    (hzero : ∀ x, Ψ 0 x = x) (n : ℕ) (τ : ℝ) (x : E)
    (hτ : |τ| * (L : ℝ) < 1) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E => flowSteps Ψ n p.1 p.2) (τ, x) := by
  induction n with
  | zero => exact contDiffAt_snd
  | succ n ih =>
    exact (flow_contDiffAt_short Z hZ hL hΨ hzero τ
      (flowSteps Ψ n τ x) hτ).comp (τ, x) (contDiffAt_fst.prodMk ih)

/-- An actual global flow of a smooth globally Lipschitz finite-dimensional
field is jointly smooth in elapsed time and the initial point. -/
theorem flow_contDiff (Z : C(E, E))
    (hZ : ContDiff ℝ ∞ (Z : E → E)) {L : ℝ≥0} (hL : LipschitzWith L Z)
    {Ψ : ℝ → E → E}
    (hΨ : ∀ t x, HasDerivAt (fun s => Ψ s x) (Z (Ψ t x)) t)
    (hzero : ∀ x, Ψ 0 x = x) :
    ContDiff ℝ ∞ (fun p : ℝ × E => Ψ p.1 p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  rintro ⟨t, x⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| * (L : ℝ) + 1)
  have hnpos : (0 : ℝ) < n := by
    have hp := mul_nonneg (abs_nonneg t) L.coe_nonneg
    linarith
  have hsmall : |t / (n : ℝ)| * (L : ℝ) < 1 := by
    rw [abs_div, abs_of_pos hnpos, div_mul_eq_mul_div, div_lt_one hnpos]
    linarith
  have hs := flowSteps_contDiffAt Z hZ hL hΨ hzero n (t / (n : ℝ)) x hsmall
  have hc : ContDiffAt ℝ ∞ (fun p : ℝ × E => (p.1 / (n : ℝ), p.2)) (t, x) :=
    (contDiffAt_fst.div_const _).prodMk contDiffAt_snd
  have he : (fun p : ℝ × E => flowSteps Ψ n (p.1 / (n : ℝ)) p.2) =
      fun p => Ψ p.1 p.2 := by
    funext p
    rw [flowSteps_eq hL hΨ hzero]
    congr 2
    field_simp [ne_of_gt hnpos]
  have hcomp := hs.comp (t, x) hc
  simpa only [Function.comp_def, he] using hcomp

end ForcedComputation.Flow

end

end OAI
