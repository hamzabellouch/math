import OAI.Probability.LatticePassage.BoundedEfronStein
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

def clipReal (n : ℕ) (a : ℝ) : ℝ := max (-(n : ℝ)) (min a n)

@[fun_prop] lemma measurable_clipReal (n : ℕ) : Measurable (clipReal n) := by
  unfold clipReal
  fun_prop

lemma clipReal_bound (n : ℕ) (a : ℝ) : |clipReal n a| ≤ n := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (min_le_right _ _)

lemma clipReal_lipschitz (n : ℕ) (a b : ℝ) : |clipReal n a-clipReal n b| ≤ |a-b| := by
  have h₁ := abs_max_sub_max_le_max (-(n : ℝ)) (min a n) (-(n : ℝ)) (min b n)
  have h₂ := abs_min_sub_min_le_max a (n : ℝ) b n
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (min a (n : ℝ)-min b n))] at h₁
  simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (a-b))] at h₂
  exact h₁.trans h₂

lemma clipReal_abs_le (n : ℕ) (a : ℝ) : |clipReal n a| ≤ |a| := by
  have h := clipReal_lipschitz n a 0
  have he : clipReal n 0 = 0 := by simp [clipReal]
  simpa only [he, sub_zero] using h

lemma clipReal_tendsto (a : ℝ) : Tendsto (fun n => clipReal n a) atTop (𝓝 a) := by
  obtain ⟨N,hN⟩ := exists_nat_ge |a|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hna : |a| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have ha := abs_le.mp hna
  simp [clipReal, min_eq_left ha.2, max_eq_right ha.1]

theorem centered_square_lintegral_le_resampling {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : (ι → α) → ℝ} (hf : Measurable f)
    (hfi : Integrable f (Measure.pi (fun _ : ι => μ))) :
    (∫⁻ v : ι → α, ENNReal.ofReal ((f v - ∫ w, f w ∂Measure.pi (fun _ : ι => μ))^2)
      ∂Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫⁻ z : (ι → α) × (ι → α),
        ENNReal.ofReal ((f (Function.update z.1 i (z.2 i))-f z.1)^2)
        ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)) := by
  let P := Measure.pi (fun _ : ι => μ)
  let F := fun n v => clipReal n (f v)
  have hFm : ∀ n, Measurable (F n) := fun n => (measurable_clipReal n).comp hf
  have hmean : Tendsto (fun n => ∫ v, F n v ∂P) atTop (𝓝 (∫ v, f v ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun v => |f v|)
      (fun n => (hFm n).aestronglyMeasurable) hfi.abs
    · intro n
      exact .of_forall (fun v => by simpa only [Real.norm_eq_abs] using clipReal_abs_le n (f v))
    · exact .of_forall (fun v => clipReal_tendsto (f v))
  let H := fun n v => ENNReal.ofReal ((F n v - ∫ w, F n w ∂P)^2)
  have hHm : ∀ n, Measurable (H n) := by intro n; dsimp [H]; fun_prop
  have hlim : ∀ v, Tendsto (fun n => H n v) atTop
      (𝓝 (ENNReal.ofReal ((f v - ∫ w, f w ∂P)^2))) := by
    intro v
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((clipReal_tendsto (f v)).sub hmean).pow 2)
  let E := ∑ i : ι, ∫⁻ z : (ι → α) × (ι → α),
    ENNReal.ofReal ((f (Function.update z.1 i (z.2 i))-f z.1)^2) ∂P.prod P
  have hbound : ∀ n, (∫⁻ v, H n v ∂P) ≤ E := by
    intro n
    apply (bounded_centered_square_lintegral μ (hFm n) (Nat.cast_nonneg n)
      (fun v => clipReal_bound n (f v))).trans
    apply sum_le_sum
    intro i _
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    have h := clipReal_lipschitz n (f (Function.update z.1 i (z.2 i))) (f z.1)
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa only [sq_abs] using hs
  change (∫⁻ v, ENNReal.ofReal ((f v - ∫ w, f w ∂P)^2) ∂P) ≤ E
  calc
    _ = ∫⁻ v, liminf (fun n => H n v) atTop ∂P :=
      lintegral_congr (fun v => (hlim v).liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ v, H n v ∂P) atTop := lintegral_liminf_le hHm
    _ ≤ E := by
      apply (liminf_le_liminf (.of_forall hbound)).trans_eq
      simp

end CompanionFPP

end OAI
