import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryReversePrices

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance likelihoodFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

def inversePenalty (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  (if i ∈ activeSteps n D then (1+selectedCost G order d x p w n D i ω m)^2 else 1) *
    max 1 (contactTotal G order d x p w n D i ω)

lemma inversePenalty_nonneg (i : Fin n) (ω : E → Bool) (m : Option E) :
    0 ≤ inversePenalty G order d x p w n D i ω m := by
  unfold inversePenalty
  exact mul_nonneg (by split_ifs; exact sq_nonneg _; exact zero_le_one)
    (le_trans zero_le_one (le_max_left _ _))

lemma supported_contactTotal_pos (s : ℕ) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n) :
    0 < contactTotal G order d x p w n D i ω := by
  have hh : 0 < scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) :=
    lt_of_le_of_ne (scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ _) <|
      Ne.symm (supported_schedule_ne_zero G order d x p w s n D ω m hz i)
  exact hh.trans_le (Finset.single_le_sum (fun k _ => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ k)
    (Finset.mem_univ (m i)))

lemma supported_stage_likelihood (s : ℕ) (hp : p ≠ 0) (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) :
    FiniteProduct.density (QueryTree.bitWeight p) (stage n D ω m i.val) =
      FiniteProduct.density (QueryTree.bitWeight p) (stage n D ω m (i.val+1)) * ((1-p)/p) := by
  obtain ⟨e,he,_⟩ := supported_active_admissible G order d x p w s n D ω m hz
    ⟨i,(Finset.mem_filter.mp hi).2⟩
  have hs : stage n D ω m (i.val+1) = Function.update (stage n D ω m i.val) e true := by
    unfold stage
    rw [stageIndices_succ_active n D i hi,opened_insert _ m ω i e he]
  have hh := density_open_likelihood p (stage n D ω m i.val) e
    (supported_stage_closed G order d x p w s n D ω m hz i hi e he)
  rw [← hs] at hh
  simpa only [mul_div_assoc] using (eq_div_iff hp).mpr hh

lemma supported_step_likelihood (s : ℕ) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n) :
    FiniteProduct.density (QueryTree.bitWeight p) (stage n D ω m i.val) *
        scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) ≤
      FiniteProduct.density (QueryTree.bitWeight p) (stage n D ω m (i.val+1)) *
        (inverseKernel G order d x p w n D i.val (stage n D ω m (i.val+1)) (masked (activeSteps n D) m i) *
          inactiveKernel G order d x p w n D i ω (masked (activeSteps n D)ᶜ m i) *
          inversePenalty G order d x p w n D i ω (m i)) := by
  have hμ : ∀ η : E → Bool, 0 ≤ FiniteProduct.density (QueryTree.bitWeight p) η :=
    FiniteProduct.density_nonneg (QueryTree.bitWeight_nonneg ⟨hp.1.le,hp.2.le⟩)
  have hr := scheduleWeight_nonneg G order d x p w hp h0 h1 n (fun j => (D j).1) i (configuration ω) (m i)
  have hA := supported_contactTotal_pos G order d x p w n D s hp h0 h1 ω m hz i
  by_cases hi : i ∈ activeSteps n D
  · obtain ⟨e,he,_⟩ := supported_active_admissible G order d x p w s n D ω m hz
      ⟨i,(Finset.mem_filter.mp hi).2⟩
    have hn := (selected_nonneg G order d x p w n D hp h0 h1 i ω (m i)).2
    have hc : (1+selectedCost G order d x p w n D i ω (m i))^2 ≠ 0 := by positivity
    have hg := supported_guess_price G order d x p w s n D hp.1.ne' ω m hz i hi e he
    have hb := supported_stage_likelihood G order d x p w n D s hp.1.ne' ω m hz i hi
    have hK : inverseKernel G order d x p w n D i.val (stage n D ω m (i.val+1))
        (masked (activeSteps n D) m i) =
        ((1-p)/p * selectedWeight G order d x p w n D i ω (m i) /
         (1+selectedCost G order d x p w n D i ω (m i))^2) := by
      simpa only [inverseKernel,dite_eq_left i.isLt,ite_eq_left hi,masked,he] using hg
    have hI : inactiveKernel G order d x p w n D i ω (masked (activeSteps n D)ᶜ m i) = 1 := by
      simp only [inactiveKernel,masked,Finset.mem_compl,hi,
        not_true_eq_false,ite_false,ite_true]
    rw [hK,hI,mul_one,supported_selected_eq G order d x p w n D s ω m hz i,
      hb,inversePenalty,ite_eq_left hi]
    have hh : ((1-p)/p * scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) /
        (1+selectedCost G order d x p w n D i ω (m i))^2) *
        ((1+selectedCost G order d x p w n D i ω (m i))^2) =
        ((1-p)/p)*scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) :=
      div_mul_cancel₀ _ hc
    have hh2 : ((1-p)/p * scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) /
        (1+selectedCost G order d x p w n D i ω (m i))^2) *
        ((1+selectedCost G order d x p w n D i ω (m i))^2 *
          max 1 (contactTotal G order d x p w n D i ω)) =
        (((1-p)/p)*scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i)) *
          max 1 (contactTotal G order d x p w n D i ω) := by
      rw [← mul_assoc,hh]
    rw [hh2]
    simpa only [mul_assoc,mul_one] using mul_le_mul_of_nonneg_left (le_max_left 1 (contactTotal G order d x p w n D i ω))
      (mul_nonneg (hμ _) (mul_nonneg (div_nonneg (sub_nonneg.mpr hp.2.le) hp.1.le) hr))
  · have hs : stage n D ω m (i.val+1) = stage n D ω m i.val := by
      unfold stage
      rw [stageIndices_succ_inactive n D i hi]
    simp only [inverseKernel,dite_eq_left i.isLt,masked,Finset.mem_compl,hi,not_false_eq_true,
      ite_true,ite_false,inactiveKernel,ite_eq_right hA.ne',inversePenalty,one_mul,hs]
    apply mul_le_mul_of_nonneg_left _ (hμ _)
    calc
      _ = (scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) /
        contactTotal G order d x p w n D i ω) * contactTotal G order d x p w n D i ω :=
          (div_mul_cancel₀ _ hA.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right 1 (contactTotal G order d x p w n D i ω)) (div_nonneg hr hA.le)

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
