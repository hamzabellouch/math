import OAI.Analysis.LipschitzHilbert.Estimates.RelativeExitScales
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! Summable quadratic energies of the relative sampled martingales. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

def relativeExitEnergy (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (x : Ω) : ℝ :=
  ∑ j : Fin H, ‖F (relativeExitTimes F a H (j.val+1) x) x-
    F (relativeExitTimes F a H j.val x) x‖^2

theorem relativeExitEnergy_nonneg (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (x : Ω) :
    0≤relativeExitEnergy F a H x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem relativeExitEnergy_bound (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (x : Ω) :
    relativeExitEnergy F a H x≤4*(H:ℝ)*(runningOscillation F H x)^2 := by
  have hb (j : Fin H) : ‖F (relativeExitTimes F a H (j.val+1) x) x-
      F (relativeExitTimes F a H j.val x) x‖≤2*runningOscillation F H x := by
    have h1 := le_runningOscillation F (relativeExitTimes_le F a H (j.val+1) x) x
    have h2 := le_runningOscillation F (relativeExitTimes_le F a H j.val x) x
    have ht := dist_triangle (F (relativeExitTimes F a H (j.val+1) x) x) (F 0 x)
      (F (relativeExitTimes F a H j.val x) x)
    simp only [dist_eq_norm] at ht
    rw [norm_sub_rev (F 0 x)] at ht
    linarith
  calc
    _ ≤ ∑ _j : Fin H, 4*(runningOscillation F H x)^2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := hb j
      have hn := norm_nonneg (F (relativeExitTimes F a H (j.val+1) x) x-
        F (relativeExitTimes F a H j.val x) x)
      nlinarith
    _ = _ := by simp; ring

theorem relativeExitScale_summable : Summable relativeExitScale :=
  summable_geometric_two.mul_left (1/4)

theorem relativeExitScale_tsum : ∑' m, relativeExitScale m=1/2 := by
  change (∑' m, (1/4:ℝ)*(1/2)^m)=1/2
  rw [tsum_mul_left,tsum_geometric_two]
  norm_num

theorem relativeExitEnergy_summable (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) :
    Summable (fun m => relativeExitScale m*relativeExitEnergy F (relativeExitScale m) H x) := by
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (relativeExitScale_pos m).le (relativeExitEnergy_nonneg F _ H x))
    (fun m => mul_le_mul_of_nonneg_left (relativeExitEnergy_bound F _ H x) (relativeExitScale_pos m).le)
  exact relativeExitScale_summable.mul_right _

def weightedRelativeExitEnergy (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) : ℝ :=
  ∑' m, relativeExitScale m*relativeExitEnergy F (relativeExitScale m) H x

theorem weightedRelativeExitEnergy_nonneg (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) :
    0≤weightedRelativeExitEnergy F H x :=
  tsum_nonneg fun m => mul_nonneg (relativeExitScale_pos m).le (relativeExitEnergy_nonneg F _ H x)

theorem weightedRelativeExitEnergy_bound (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) :
    weightedRelativeExitEnergy F H x≤2*(H:ℝ)*(runningOscillation F H x)^2 := by
  calc
    _ ≤ ∑' m, relativeExitScale m*(4*(H:ℝ)*(runningOscillation F H x)^2) :=
      Summable.tsum_le_tsum
        (fun m => mul_le_mul_of_nonneg_left (relativeExitEnergy_bound F _ H x) (relativeExitScale_pos m).le)
        (relativeExitEnergy_summable F H x) (relativeExitScale_summable.mul_right _)
    _ = _ := by rw [tsum_mul_right,relativeExitScale_tsum]; ring

section Measure
variable [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}

theorem relativeExitEnergy_measurable (hF : StronglyAdapted ℱ F) (a : ℝ) (H : ℕ) :
    Measurable (relativeExitEnergy F a H) := by
  have hs (j : ℕ) : Measurable (fun x => F (relativeExitTimes F a H j x) x) := by
    have ht := stronglyMeasurable_stoppedValue_of_le hF.isStronglyProgressive_of_discrete
      (relativeExitTimes_isStopping F hF a H j) (fun x => by
        change (relativeExitTimes F a H j x:WithTop ℕ)≤(H:WithTop ℕ)
        exact_mod_cast relativeExitTimes_le F a H j x)
    exact (ht.mono (ℱ.le H)).measurable
  exact Finset.measurable_sum _ (fun j _ => ((hs (j.val+1)).sub (hs j.val)).norm.pow_const 2)

omit [IsFiniteMeasure μ] in
theorem relativeExitEnergy_integrable (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (a : ℝ) (H : ℕ) :
    Integrable (relativeExitEnergy F a H) μ := by
  have hs (j : ℕ) : MemLp (fun x => F (relativeExitTimes F a H j x) x) 2 μ :=
    memLp_stoppedValue (relativeExitTimes_isStopping F hF.1 a H j) hF2 (fun x => by
      change (relativeExitTimes F a H j x:WithTop ℕ)≤(H:WithTop ℕ)
      exact_mod_cast relativeExitTimes_le F a H j x)
  apply integrable_finsetSum
  intro j _
  have hi := ((hs (j.val+1)).sub (hs j.val)).integrable_sq
  convert hi using 1; ext x; simp [Real.norm_eq_abs,sq_abs,Pi.sub_apply]

theorem relativeExitEnergy_integral_le (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (a : ℝ) (ha : 0≤a) (H : ℕ) :
    (∫ x, relativeExitEnergy F a H x ∂μ)≤∫ x, F H x^2 ∂μ := by
  let τ := fun j x => (relativeExitTimes F a H j x:WithTop ℕ)
  have ht (j : ℕ) : IsStoppingTime ℱ (τ j) := relativeExitTimes_isStopping F hF.1 a H j
  have hm (j : ℕ) : τ j≤τ (j+1) := fun x => by
    change (relativeExitTimes F a H j x:WithTop ℕ)≤(relativeExitTimes F a H (j+1) x:WithTop ℕ)
    exact_mod_cast relativeExitTimes_mono F a ha H x (Nat.le_succ j)
  have hb (j : ℕ) (x : Ω) : τ j x≤H := by
    change (relativeExitTimes F a H j x:WithTop ℕ)≤(H:WithTop ℕ)
    exact_mod_cast relativeExitTimes_le F a H j x
  have he := stopped_martingale_chain_energy hF hF2 τ ht hm H H hb
  have hs (j : Fin H) : Integrable (fun x =>
      ‖F (relativeExitTimes F a H (j.val+1) x) x-F (relativeExitTimes F a H j.val x) x‖^2) μ := by
    have hi :=
      ((memLp_stoppedValue (ht (j.val+1)) hF2 (hb (j.val+1))).sub
        (memLp_stoppedValue (ht j.val) hF2 (hb j.val))).integrable_sq
    change Integrable (fun x => (F (relativeExitTimes F a H (j.val+1) x) x-
      F (relativeExitTimes F a H j.val x) x)^2) μ at hi
    simpa only [Real.norm_eq_abs,sq_abs] using hi
  change (∫ x, ∑ j : Fin H, ‖F (relativeExitTimes F a H (j.val+1) x) x-
    F (relativeExitTimes F a H j.val x) x‖^2 ∂μ)≤_
  rw [integral_finsetSum _ (fun j _ => hs j)]
  change (∑ i∈Finset.range H, ∫ x, (F (relativeExitTimes F a H (i+1) x) x-
    F (relativeExitTimes F a H i x) x)^2 ∂μ)≤_ at he
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∫ x, (F (relativeExitTimes F a H (i+1) x) x-
    F (relativeExitTimes F a H i x) x)^2 ∂μ) H] at he
  simpa only [Real.norm_eq_abs,sq_abs] using he


theorem weightedRelativeExitEnergy_measurable (hF : StronglyAdapted ℱ F) (H : ℕ) :
    Measurable (weightedRelativeExitEnergy F H) :=
  Measurable.tsum (fun k => (relativeExitEnergy_measurable hF (relativeExitScale k) H).const_mul _)

omit [IsFiniteMeasure μ] in
theorem weightedRelativeExitEnergy_integrable (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (H : ℕ) :
    Integrable (weightedRelativeExitEnergy F H) μ := by
  have hr : MemLp (runningOscillation F H) 2 μ :=
    finiteMaxSignal_memLp μ _ H (fun n => (hF2 n).sub (hF2 0))
  apply (hr.integrable_sq.const_mul (2*(H:ℝ))).mono'
    (weightedRelativeExitEnergy_measurable hF.1 H).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (weightedRelativeExitEnergy_nonneg F H x)]
  exact weightedRelativeExitEnergy_bound F H x

theorem weightedRelativeExitEnergy_integral_le (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (H : ℕ) :
    (∫ x, weightedRelativeExitEnergy F H x ∂μ)≤(1/2)*(∫ x, F H x^2 ∂μ) := by
  let G := fun k x => relativeExitScale k*relativeExitEnergy F (relativeExitScale k) H x
  have hg (k : ℕ) : Integrable (G k) μ :=
    (relativeExitEnergy_integrable hF hF2 (relativeExitScale k) H).const_mul _
  have hgn (k : ℕ) (x : Ω) : 0≤G k x :=
    mul_nonneg (relativeExitScale_pos k).le (relativeExitEnergy_nonneg F _ H x)
  have hle (k : ℕ) : (∫ x, G k x ∂μ)≤relativeExitScale k*(∫ x, F H x^2 ∂μ) := by
    rw [show (∫ x, G k x ∂μ)=relativeExitScale k*(∫ x, relativeExitEnergy F (relativeExitScale k) H x ∂μ)
      from integral_const_mul _ _]
    exact mul_le_mul_of_nonneg_left (relativeExitEnergy_integral_le hF hF2 _ (relativeExitScale_pos k).le H)
      (relativeExitScale_pos k).le
  have hs : Summable (fun k => ∫ x, G k x ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg (hgn k)) hle
      (relativeExitScale_summable.mul_right _)
  have hsn : Summable (fun k => ∫ x, ‖G k x‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (hgn _ _)] using hs
  change (∫ x, ∑' k, G k x ∂μ)≤_
  rw [← integral_tsum_of_summable_integral_norm hg hsn]
  calc
    _ ≤ ∑' k, relativeExitScale k*(∫ x, F H x^2 ∂μ) :=
      Summable.tsum_le_tsum hle hs (relativeExitScale_summable.mul_right _)
    _ = _ := by rw [tsum_mul_right,relativeExitScale_tsum]

end Measure
end LipschitzHilbert

end

end OAI
