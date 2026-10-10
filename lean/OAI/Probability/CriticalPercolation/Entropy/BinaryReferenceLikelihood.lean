import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.RecursiveLikelihood
import OAI.Probability.CriticalPercolation.Entropy.BinaryLikelihood

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance refLikelihoodFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

noncomputable def recorded (n : ℕ) (D : FixedDescriptor n) (z : (E → Bool) × (Fin n → Option E)) :
    (E → Bool) × (Fin n → Option E) × (Fin n → Option E) :=
  (stage n D z.1 z.2 n,masked (activeSteps n D) z.2,masked (activeSteps n D)ᶜ z.2)

variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

def inverseLog (ω : E → Bool) (m : Fin n → Option E) : ℝ :=
  2*(∑ i ∈ activeSteps n D, Real.log (1+selectedCost G order d x p w n D i ω (m i))) +
    logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1)) (configuration ω)

lemma inversePenalty_product (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (m : Fin n → Option E) :
    (∏ i, inversePenalty G order d x p w n D i ω (m i)) =
      Real.exp (inverseLog G order d x p w n D ω m) := by
  have hc (i : Fin n) : 0 < 1+selectedCost G order d x p w n D i ω (m i) := by
    have hn := (selected_nonneg G order d x p w n D hp h0 h1 i ω (m i)).2
    linarith
  have he (i : Fin n) : (if i ∈ activeSteps n D then
      (1+selectedCost G order d x p w n D i ω (m i))^2 else 1) =
      Real.exp (if i ∈ activeSteps n D then
        2*Real.log (1+selectedCost G order d x p w n D i ω (m i)) else 0) := by
    split_ifs
    · rw [two_mul,Real.exp_add,Real.exp_log (hc i),pow_two]
    · exact Real.exp_zero.symm
  simp only [inversePenalty,Finset.prod_mul_distrib,he,← Real.exp_sum]
  change _ * (∏ i, max 1 (∑ a, scheduleWeight G order d x p w n
    (fun j => (D j).1) i (configuration ω) a)) = _
  rw [← exp_logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1))
    (configuration ω),← Real.exp_add]
  congr 1
  simp only [inverseLog,logContactMass]
  rw [← Finset.sum_filter,← Finset.mul_sum]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]

lemma supported_reference_dominance (s : ℕ) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) :
    FiniteProduct.density (QueryTree.bitWeight p) ω *
        (∏ i, scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i)) ≤
      inverseReference G order d x p w n D (recorded n D (ω,m)) *
        Real.exp (inverseLog G order d x p w n D ω m) := by
  let m' : ℕ → Option E := fun j => if hj : j<n then masked (activeSteps n D) m ⟨j,hj⟩ else none
  have hm : (fun i : Fin n => m' i.val) = masked (activeSteps n D) m := by
    funext i
    simp only [m',dite_eq_left i.isLt]
  have hu : ∀ j<n, inverseUpdate (E := E) n D j (stage n D ω m (j+1)) (m' j) = stage n D ω m j := by
    intro j hj
    simpa only [m',dite_eq_left hj] using supported_inverse_update G order d x p w s n D ω m hz ⟨j,hj⟩
  have hh := ReverseReference.joint_trajectory_dominance
    (FiniteProduct.density (QueryTree.bitWeight p) : (E → Bool) → ℝ)
    (inverseKernel G order d x p w n D) (inverseUpdate (E := E) n D) n
    (inactiveKernel G order d x p w n D) (stage n D ω m) m' (masked (activeSteps n D)ᶜ m)
    (fun i => scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i))
    (fun i => inversePenalty G order d x p w n D i ω (m i)) hu
    (fun i => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ _)
    (fun i => mul_nonneg (mul_nonneg
      (inverseKernel_nonneg G order d x p w n D hp h0 h1 _ _ _)
      (inactiveKernel_nonneg G order d x p w n D hp h0 h1 _ _ _))
      (inversePenalty_nonneg G order d x p w n D _ _ _))
    (fun i => by
      simpa only [stage_zero,m',dite_eq_left i.isLt] using
        supported_step_likelihood G order d x p w n D s hp h0 h1 ω m hz i)
  rw [hm,stage_zero,inversePenalty_product G order d x p w n D hp h0 h1 ω m] at hh
  exact hh

lemma conditioned_reference_density_le (s : ℕ) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D)
    (z : (E → Bool) × (Fin n → Option E)) :
    conditionedMass G order d x p w s n D z ≤
      inverseReference G order d x p w n D (recorded n D z) *
      Real.exp (constructionCost G order d x p w c s n D + inverseLog G order d x p w n D z.1 z.2) := by
  by_cases hz : conditionedMass G order d x p w s n D z = 0
  · rw [hz]
    exact mul_nonneg (inverseReference_nonneg G order d x p w n D hp h0 h1 _) (Real.exp_pos _).le
  · have hh := mul_le_mul_of_nonneg_left
      (supported_reference_dominance G order d x p w n D s hp h0 h1 z.1 z.2 hz)
      (Real.exp_pos (constructionCost G order d x p w c s n D)).le
    calc
      _ ≤ _ := conditionedMass_density_le G order d x p w hd hp h0 h1 hc hc1 hconn s n D hδ hD z
      _ ≤ _ := by simpa only [Real.exp_add,mul_assoc,mul_left_comm,mul_comm] using hh

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
