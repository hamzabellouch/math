import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.AmbientGram

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression
section Stochastic
variable {J X : Type*} [Fintype J] {d : ℕ}

def stochRoute (δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞) (n : ℕ) :
    (k : ℕ) → J → ((Fin k → Space d) × (Fin k → ℝ)) → J → ℝ≥0∞
  | 0, j, _, w => by classical exact if j = w then 1 else 0
  | k+1, j, x, w => ∑ a, δ (n+1) j (x.1 0,x.2 0) a *
      stochRoute δ (n+1) k a (Fin.tail x.1,Fin.tail x.2) w

lemma measurable_stochRoute {δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞}
    (hδ : ∀ n j a, Measurable (fun obs => δ n j obs a)) (n k : ℕ) (j w : J) :
    Measurable (fun x => stochRoute δ n k j x w) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    apply Finset.measurable_sum _
    intro a _
    exact ((hδ (n+1) j a).comp (by fun_prop)).mul ((ih (n+1) a).comp (by fun_prop))

lemma stochRoute_sum_le_one {δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞}
    (hδ : ∀ n j obs, ∑ a, δ n j obs a ≤ 1) (n k : ℕ) (j : J)
    (x : (Fin k → Space d) × (Fin k → ℝ)) : ∑ w, stochRoute δ n k j x w ≤ 1 := by
  classical
  induction k generalizing n j with
  | zero => simp [stochRoute]
  | succ k ih =>
    simp only [stochRoute]
    rw [Finset.sum_comm]
    calc
      _ = ∑ a, δ (n+1) j (x.1 0,x.2 0) a *
        (∑ w, stochRoute δ (n+1) k a (Fin.tail x.1,Fin.tail x.2) w) := by simp [Finset.mul_sum]
      _ ≤ ∑ a, δ (n+1) j (x.1 0,x.2 0) a := Finset.sum_le_sum (fun a _ =>
        mul_le_of_le_one_right' (ih (n+1) a _))
      _ ≤ 1 := hδ _ _ _

def stochCont (δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞)
    (w : ℕ → J → X → ℝ≥0∞) (ι : X → Space d) (n : ℕ) : ℕ → J → X → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, ∑ a, δ (n+1) j (x,⟪ι s,x⟫) a *
      stochCont δ w ι (n+1) k a s ∂stdGaussian (Space d)

lemma measurable_stochCont [MeasurableSpace X] {δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞}
    {w : ℕ → J → X → ℝ≥0∞} {ι : X → Space d}
    (hδ : ∀ n j a, Measurable (fun obs => δ n j obs a))
    (hw : ∀ n j, Measurable (w n j)) (hι : Measurable ι) (n k : ℕ) (j : J) :
    Measurable (stochCont δ w ι n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    exact Finset.measurable_sum _ (fun a _ =>
      ((hδ (n+1) j a).comp (by fun_prop)).mul ((ih (n+1) a).comp measurable_snd))

lemma stochCont_le_one {δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞}
    {w : ℕ → J → X → ℝ≥0∞} (ι : X → Space d)
    (hδ : ∀ n j obs, ∑ a, δ n j obs a ≤ 1)
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : J) (s : X) :
    stochCont δ w ι n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih =>
    apply (lintegral_mono (fun x => (Finset.sum_le_sum
      (fun a _ => mul_le_of_le_one_right' (ih (n+1) a))).trans (hδ _ _ _))).trans_eq
    simp

lemma stochCont_unroll {δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞}
    {w : ℕ → J → X → ℝ≥0∞} (ι : X → Space d)
    (hδ : ∀ n j a, Measurable (fun obs => δ n j obs a))
    (n m k : ℕ) (j : J) (s : X) :
    stochCont δ w ι n (m+k) j s =
      ∫⁻ A : Fin m → Space d, ∑ a, stochRoute δ n m j (A,fun i => ⟪ι s,A i⟫) a *
        stochCont δ w ι (n+m) k a s ∂Measure.pi (fun _ => stdGaussian (Space d)) := by
  classical
  induction m generalizing n j with
  | zero => simp [stochRoute]
  | succ m ih =>
    rw [Nat.succ_add, stochCont]
    simp_rw [ih]
    have hf : Measurable (fun A : Fin (m+1) → Space d => ∑ a,
        stochRoute δ n (m+1) j (A,fun i => ⟪ι s,A i⟫) a *
          stochCont δ w ι (n+(m+1)) k a s) := by
      exact Finset.measurable_sum _ (fun a _ =>
        ((measurable_stochRoute hδ n (m+1) j a).comp (by fun_prop)).mul measurable_const)
    rw [lintegral_pi_cons _ _ hf]
    apply lintegral_congr
    intro x
    have hm (a : J) : Measurable (fun A : Fin m → Space d => ∑ b,
        stochRoute δ (n+1) m a (A,fun i => ⟪ι s,A i⟫) b *
          stochCont δ w ι (n+1+m) k b s) := by
      exact Finset.measurable_sum _ (fun b _ =>
        ((measurable_stochRoute hδ (n+1) m a b).comp (by fun_prop)).mul measurable_const)
    simp_rw [← lintegral_const_mul _ (hm _)]
    rw [← lintegral_finsetSum _ (fun a _ => (hm a).const_mul _)]
    apply lintegral_congr
    intro A
    simp only [stochRoute, Fin.cons_zero, Fin.tail_cons]
    have het : Fin.tail (fun i : Fin (m+1) => ⟪ι s,(Fin.cons x A : Fin (m+1) → Space d) i⟫) =
        (fun i => ⟪ι s,A i⟫) := rfl
    rw [het]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    congr 1
    funext a
    congr 1
    funext b
    simp [Nat.add_comm, Nat.add_left_comm]

end Stochastic
end MemoryPrecision


end

end OAI
