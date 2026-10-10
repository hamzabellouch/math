import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace MahlerStokes

/-- The squared Euclidean radius, in real coordinates with standard Lebesgue measure. -/
def radiusSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2
/-- An actual Euclidean ball in coordinates; the ambient Pi norm is irrelevant. -/
def coordBall (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) := {x | radiusSq x < R ^ 2}
def chord {n : ℕ} (R : ℝ) (y : Fin n → ℝ) : ℝ := Real.sqrt (R ^ 2 - radiusSq y)

lemma radiusSq_insertNth {n : ℕ} (i : Fin (n+1)) (t : ℝ) (y : Fin n → ℝ) :
    radiusSq (i.insertNth t y) = t ^ 2 + radiusSq y := by
  unfold radiusSq
  rw [Fin.sum_univ_succAbove _ i]
  simp

lemma measurableSet_coordBall (n : ℕ) (R : ℝ) : MeasurableSet (coordBall n R) := by
  apply IsOpen.measurableSet
  exact isOpen_lt (by unfold radiusSq; fun_prop) continuous_const

lemma ball_slice {n : ℕ} (i : Fin (n+1)) (R : ℝ) (y : Fin n → ℝ) :
    {t : ℝ | i.insertNth t y ∈ coordBall (n+1) R} = Ioo (-chord R y) (chord R y) := by
  ext t
  simp only [coordBall, mem_ofPred_eq, radiusSq_insertNth, mem_Ioo, chord]
  by_cases h : 0 ≤ R ^ 2 - radiusSq y
  · rw [← abs_lt, ← Real.sqrt_sq_eq_abs t, Real.sqrt_lt_sqrt_iff (sq_nonneg t)]
    constructor <;> intro ht <;> linarith
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
    constructor
    · intro ht; nlinarith [sq_nonneg t]
    · intro ht; linarith

/-- Fubini in the i-th coordinate, for an actual restricted Lebesgue integral. -/
theorem setIntegral_slice {n : ℕ} (i : Fin (n+1)) {s : Set (Fin (n+1) → ℝ)}
    (hs : MeasurableSet s) (f : (Fin (n+1) → ℝ) → ℝ) (hf : IntegrableOn f s) :
    (∫ x in s, f x) = ∫ y : Fin n → ℝ, ∫ t in {t | i.insertNth t y ∈ s}, f (i.insertNth t y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => s.indicator f (i.insertNth p.1 p.2)) :=
    (hp.integrable_comp_emb e.symm.measurableEmbedding).2 (hf.integrable_indicator hs)
  calc
    (∫ x in s, f x) = ∫ p : ℝ × (Fin n → ℝ), s.indicator f (i.insertNth p.1 p.2) := by
      rw [← integral_indicator hs]
      exact (hp.integral_comp e.symm.measurableEmbedding (s.indicator f)).symm
    _ = ∫ y : Fin n → ℝ, ∫ t : ℝ, s.indicator f (i.insertNth t y) := (integral_prod _ hint).trans (integral_integral_swap hint)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      change _ = ∫ t in (fun t : ℝ => i.insertNth t y) ⁻¹' s, f (i.insertNth t y)
      rw [← integral_indicator (hs.preimage (by fun_prop : Measurable (fun t : ℝ => i.insertNth t y)))]
      congr 1

lemma coordBall_subset_cube {n : ℕ} (R : ℝ) :
    coordBall n R ⊆ Icc (fun _ => -|R|) (fun _ => |R|) := by
  intro x hx
  have hx' : radiusSq x < R ^ 2 := hx
  have hi (i : Fin n) : |x i| < |R| := by
    have hs : x i ^ 2 ≤ radiusSq x := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    nlinarith [sq_abs (x i), sq_abs R, abs_nonneg (x i), abs_nonneg R]
  exact ⟨fun i => (abs_lt.mp (hi i)).1.le, fun i => (abs_lt.mp (hi i)).2.le⟩

lemma integrableOn_coordBall {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) (R : ℝ) : IntegrableOn f (coordBall n R) :=
  (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set (coordBall_subset_cube R)

lemma hasDerivAt_insertNth {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (i.insertNth s y : Fin (n+1) → ℝ)) (Pi.single i 1) t := by
  have he : (fun s : ℝ => (i.insertNth s y : Fin (n+1) → ℝ)) =
      Function.update (i.insertNth (0 : ℝ) y : Fin (n+1) → ℝ) i := by
    funext s
    apply funext
    rw [i.forall_iff_succAbove]
    constructor
    · simp
    · intro j; simp
  rw [he]
  exact hasDerivAt_update _ i t

/-- Divergence for one component on an actual Euclidean ball, by integration
along coordinate chords. Each boundary term is an ordinary Lebesgue integral
on a hemisphere parameter domain; its sign is outward from the ball. -/
theorem integral_partial_coordBall {n : ℕ} (i : Fin (n+1)) (R : ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : Differentiable ℝ f)
    (hg : Continuous (fun x => fderiv ℝ f x (Pi.single i 1))) :
    (∫ x in coordBall (n+1) R, fderiv ℝ f x (Pi.single i 1)) =
      ∫ y in coordBall n R,
        f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y) := by
  rw [setIntegral_slice i (measurableSet_coordBall _ _) _ (integrableOn_coordBall hg R)]
  have he (y : Fin n → ℝ) :
      (∫ t in {t | i.insertNth t y ∈ coordBall (n+1) R}, fderiv ℝ f (i.insertNth t y) (Pi.single i 1)) =
        f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y) := by
    rw [ball_slice]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (i.insertNth t y) (Pi.single i 1)) :=
      hg.comp (by fun_prop)
    have hd (t : ℝ) := (hf (i.insertNth t y)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth i y t)
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (neg_le_self (Real.sqrt_nonneg _) : -chord R y ≤ chord R y)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable _ _)
  simp_rw [he]
  rw [← integral_indicator (measurableSet_coordBall n R)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ coordBall n R
  · simp [hy]
  · have hz : chord R y = 0 := Real.sqrt_eq_zero_of_nonpos (by change ¬radiusSq y < R^2 at hy; linarith)
    simp [hy, hz]

/-- Actual divergence equals the sum of oriented hemisphere-coordinate fluxes. -/
theorem integral_divergence_coordBall {n : ℕ} (R : ℝ)
    (F : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hF : ∀ i, Differentiable ℝ (F i))
    (hD : ∀ i, Continuous (fun x => fderiv ℝ (F i) x (Pi.single i 1))) :
    (∫ x in coordBall (n+1) R, ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) =
      ∑ i, ∫ y in coordBall n R,
        F i (i.insertNth (chord R y) y) - F i (i.insertNth (-chord R y) y) := by
  rw [integral_finsetSum _ (fun i _ => integrableOn_coordBall (hD i) R)]
  exact Finset.sum_congr rfl (fun i _ => integral_partial_coordBall i R (F i) (hF i) (hD i))

end MahlerStokes

end

end OAI
