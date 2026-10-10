import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.KernelEvaluation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)
variable {X : Type*} [MeasurableSpace X]
variable (w : ℕ → State M → X → ℝ≥0∞) (ι : X → Vector d)

lemma measurable_records_at (s : X) (k : ℕ) :
    Measurable (fun A : Rows d k => ((s, (fun i => (A i,⟪ι s,A i⟫))) : X × Observations d k)) := by
  exact measurable_const.prodMk
    (Measurable.of_eval (fun index => (measurable_pi_apply index).prodMk (by fun_prop)))

lemma cont_eq_integral (hK : K.Borel) (hw : ∀ n j, Measurable (w n j))
    (n k : ℕ) (j : State M) (s : X) :
    K.cont w ι n k j s =
      ∫⁻ A : Rows d k, K.eval w n k j s (fun i => (A i,⟪ι s,A i⟫)) ∂(RowLaw d k) := by
  classical
  induction k generalizing n j with
  | zero => simp [cont, eval, RowLaw]
  | succ k ih =>
    have hf : Measurable (fun A : Rows d (k+1) =>
        K.eval w n (k+1) j s (fun i => (A i,⟪ι s,A i⟫))) := by
      exact (K.measurable_eval w hK hw n (k+1) j).comp (measurable_records_at ι s (k+1))
    rw [RowLaw, NoiselessRegression.lintegral_pi_cons _ _ hf]
    unfold cont
    apply lintegral_congr
    intro x
    simp only [eval, Fin.cons_zero]
    have hm (a : Action M) : Measurable (fun A : Rows d k =>
        if a.1 then w (n+1) a.2 s
        else K.eval w (n+1) k a.2 s (fun i => (A i,⟪ι s,A i⟫))) := by
      rcases a with ⟨b,a⟩
      cases b
      · exact (K.measurable_eval w hK hw (n+1) k a).comp (measurable_records_at ι s k)
      · exact measurable_const
    change (∑ a : Action M, K.transition (n+1) j (x,⟪ι s,x⟫) a *
      if a.1 then w (n+1) a.2 s else K.cont w ι (n+1) k a.2 s) =
      ∫⁻ A : Rows d k, ∑ a : Action M, K.transition (n+1) j (x,⟪ι s,x⟫) a *
        if a.1 then w (n+1) a.2 s
        else K.eval w (n+1) k a.2 s (fun i => (A i,⟪ι s,A i⟫))
        ∂Measure.pi (fun _ => stdGaussian (Vector d))
    rw [lintegral_finsetSum _ (fun a _ => (hm a).const_mul _)]
    apply Finset.sum_congr rfl
    intro a _
    rw [lintegral_const_mul _ (hm a)]
    congr 1
    rcases a with ⟨b,a⟩
    cases b
    · exact ih (n+1) a
    · simp

lemma pathValue_integral_le (hK : K.Borel) (hw : ∀ n j, Measurable (w n j))
    (s : X) :
    (∫⁻ A : Rows d T, K.pathValue w s (fun i => (A i,⟪ι s,A i⟫)) ∂(RowLaw d T)) ≤
      ∑ a : Action M, K.initial a *
        (∑ r ∈ Finset.range (T+1), MemoryPrecision.stochCont K.marginal w ι 0 r a.2 s) := by
  classical
  have hm (a : Action M) : Measurable (fun A : Rows d T =>
      if a.1 then w 0 a.2 s else K.eval w 0 T a.2 s (fun i => (A i,⟪ι s,A i⟫))) := by
    rcases a with ⟨b,a⟩
    cases b
    · exact (K.measurable_eval w hK hw 0 T a).comp (measurable_records_at ι s T)
    · exact measurable_const
  unfold pathValue
  rw [lintegral_finsetSum _ (fun a _ => (hm a).const_mul _)]
  apply Finset.sum_le_sum
  intro a _
  rw [lintegral_const_mul _ (hm a)]
  apply mul_le_mul' le_rfl
  rcases a with ⟨b,a⟩
  cases b
  · change (∫⁻ A : Rows d T, K.eval w 0 T a s (fun i => (A i,⟪ι s,A i⟫)) ∂(RowLaw d T)) ≤ _
    rw [← K.cont_eq_integral w ι hK hw 0 T a s]
    exact K.cont_le_forced_sum w ι hK 0 T a s
  · change (∫⁻ _A : Rows d T, w 0 a s ∂(RowLaw d T)) ≤ _
    rw [lintegral_const]
    have : IsProbabilityMeasure (RowLaw d T) := by unfold RowLaw; infer_instance
    simp only [measure_univ, mul_one]
    simpa only [MemoryPrecision.stochCont] using
      (Finset.single_le_sum (fun length _ =>
        (show (0:ℝ≥0∞) ≤ MemoryPrecision.stochCont K.marginal w ι 0 length a s from zero_le))
        (show 0 ∈ Finset.range (T+1) by simp) :
          MemoryPrecision.stochCont K.marginal w ι 0 0 a s ≤
            ∑ r ∈ Finset.range (T+1), MemoryPrecision.stochCont K.marginal w ι 0 r a s)

lemma experiment_fixed_measurable (hK : K.Borel)
    {f : Sphere d × Sphere d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : Sphere d × Rows d T => K.pathValue (K.outputTest f) z.1 (records z.1 z.2)) := by
  apply Finset.measurable_sum _
  intro a _
  apply Measurable.const_mul
  rcases a with ⟨b,a⟩
  cases b
  · exact (K.measurable_eval (K.outputTest f) hK (K.outputTest_measurable hf) 0 T a).comp (by
      exact measurable_fst.prodMk (Measurable.of_eval (fun index => by
        change Measurable (fun z : Sphere d × Rows d T => (z.2 index,⟪z.1.val,z.2 index⟫))
        fun_prop)))
  · exact (K.outputTest_measurable hf 0 a).comp measurable_fst

lemma integral_pathValue_bound (hK : K.Borel) (hw : ∀ n j, Measurable (w n j))
    (hι : Measurable ι) (ν : Measure X) {B : ℝ≥0∞}
    (hb : ∀ (r : ℕ), r ≤ T → ∀ j,
      (∫⁻ s, MemoryPrecision.stochCont K.marginal w ι 0 r j s ∂ν) ≤ B) :
    (∫⁻ s, ∫⁻ A : Rows d T, K.pathValue w s (fun i => (A i,⟪ι s,A i⟫)) ∂(RowLaw d T) ∂ν) ≤
      (T+1:ℝ≥0∞) * B := by
  classical
  have hm (a : Action M) : Measurable (fun s =>
      ∑ r ∈ Finset.range (T+1), MemoryPrecision.stochCont K.marginal w ι 0 r a.2 s) :=
    Finset.measurable_sum _ (fun r _ =>
      MemoryPrecision.measurable_stochCont (K.marginal_measurable hK) hw hι 0 r a.2)
  calc
    _ ≤ ∫⁻ s, ∑ a : Action M, K.initial a *
        (∑ r ∈ Finset.range (T+1), MemoryPrecision.stochCont K.marginal w ι 0 r a.2 s) ∂ν :=
      lintegral_mono (K.pathValue_integral_le w ι hK hw)
    _ = ∑ a : Action M, K.initial a *
        (∑ r ∈ Finset.range (T+1), ∫⁻ s,
          MemoryPrecision.stochCont K.marginal w ι 0 r a.2 s ∂ν) := by
      rw [lintegral_finsetSum _ (fun a _ => (hm a).const_mul _)]
      apply Finset.sum_congr rfl
      intro a _
      rw [lintegral_const_mul _ (hm a), lintegral_finsetSum _ (fun r _ =>
        MemoryPrecision.measurable_stochCont (K.marginal_measurable hK) hw hι 0 r a.2)]
    _ ≤ ∑ a : Action M, K.initial a * ((T+1:ℝ≥0∞)*B) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul' le_rfl
      calc
        _ ≤ ∑ _r ∈ Finset.range (T+1), B := Finset.sum_le_sum (fun r hr => hb r (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hr)) a.2)
        _ = _ := by simp [nsmul_eq_mul]
    _ = _ := by rw [← Finset.sum_mul, K.initial_sum, one_mul]
end Policy
end MemoryPrecision.Kernel


end

end OAI
