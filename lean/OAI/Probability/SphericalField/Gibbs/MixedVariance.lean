import Mathlib
import OAI.Probability.SphericalField.Perceptron.Variance
import OAI.Probability.SphericalField.Gibbs.RootVariance

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace

namespace SphericalPerceptron
section GeneralProductVariance
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma variance_prod_le_memLp {F : X × Y → ℝ}
    (hp : MemLp F 2 (μ.prod ν)) (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hh : MemLp (fun x => ∫ y, F (x,y) ∂ν) 2 μ) {A B : ℝ}
    (hA : ∀ x, variance (fun y => F (x,y)) ν ≤ A)
    (hB : variance (fun x => ∫ y, F (x,y) ∂ν) μ ≤ B) :
    variance F (μ.prod ν) ≤ A+B := by
  have hi : (∫ x, ∫ y, F (x,y)^2 ∂ν ∂μ) ≤ A+∫ x, (∫ y, F (x,y) ∂ν)^2 ∂μ := by
    calc
      _ ≤ ∫ x, (A+(∫ y, F (x,y) ∂ν)^2) ∂μ := by
        apply integral_mono hp.integrable_sq.integral_prod_left
          ((integrable_const A).add hh.integrable_sq)
        intro x
        have hv := hA x
        rw [variance_eq_sub (hs x)] at hv
        simpa only [Pi.pow_apply, Pi.add_apply] using sub_le_iff_le_add.mp hv
      _ = _ := by rw [integral_add (integrable_const _) hh.integrable_sq]; simp
  rw [variance_eq_sub hh] at hB
  rw [variance_eq_sub hp]
  simp only [Pi.pow_apply] at hB ⊢
  rw [integral_prod _ hp.integrable_sq,
    integral_prod _ (hp.integrable (by norm_num))]
  linarith

end GeneralProductVariance

section MixedRoot
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_bound {W : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hVm : Measurable V) {K C : ℝ}
    (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    |vectorLogPartition ρ W V x| ≤ K+C*‖x‖ := by
  have hh := abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (show Integrable (fun _ : S => Real.exp 0) ρ by simp)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (show 0 < ∫ _ : S, Real.exp 0 ∂ρ by simp)
    (c := K+C*‖x‖) (fun s => by simpa using vectorEnergy_bound hW hV x s)
  simpa [vectorLogPartition,vectorPartition] using hh

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_data_bound {W W' : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hWm' : Measurable W') (hVm : Measurable V) {K K' C c : ℝ}
    (hW : ∀ s, |W s| ≤ K) (hW' : ∀ s, |W' s| ≤ K') (hV : ∀ s, ‖V s‖ ≤ C)
    (hWc : ∀ s, |W s-W' s| ≤ c) (x : E) :
    |vectorLogPartition ρ W V x-vectorLogPartition ρ W' V x| ≤ c := by
  exact abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (vectorPartition_integrable ρ hWm' hVm hW' hV x)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (vectorPartition_pos ρ hWm' hVm hW' hV x)
    (fun s => by simpa only [add_sub_add_right_eq_sub] using hWc s)

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Nonempty X] (μ : Measure X) [IsProbabilityMeasure μ]

lemma vectorLogPartition_mixed_variance (n : ℕ)
    {W : (Fin n → X) → S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable (Function.uncurry W)) (hWc : ∀ s, Continuous (fun p => W p s))
    (hVm : Measurable V) {K C c : ℝ} (hC : 0 ≤ C)
    (hW : ∀ p s, |W p s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)
    (hosc : ∀ p i z s, |W (Function.update p i z) s-W p s| ≤ c) :
    variance (fun p => vectorLogPartition ρ (W p.1) V p.2)
      ((Measure.pi fun _ : Fin n => μ).prod (stdGaussian E)) ≤
      Real.pi^2/8*C^2+(n:ℝ)*c^2 := by
  classical
  let ν := Measure.pi (fun _ : Fin n => μ)
  let γ := stdGaussian E
  let F := fun (p : Fin n → X) (g : E) => vectorLogPartition ρ (W p) V g
  have hWm' (p) : Measurable (W p) := hWm.comp (measurable_const.prodMk measurable_id)
  have hFm : Measurable (Function.uncurry F) := by
    have hm : Measurable (fun p : ((Fin n → X)×E)×S =>
        Real.exp (W p.1.1 p.2+V p.2 p.1.2)) := by
      apply Measurable.exp
      exact (hWm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).add
        (((continuous_fst.clm_apply continuous_snd : Continuous
          (fun p : StrongDual ℝ E × E => p.1 p.2)).measurable).comp
          ((hVm.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable.log
  have hFB (p) (g) : |F p g| ≤ K+C*‖g‖ :=
    vectorLogPartition_bound ρ (hWm' p) hVm (hW p) hV g
  have hGB : MemLp (fun g : E => K+C*‖g‖) 2 γ := by
    exact (memLp_const K).add ((IsGaussian.memLp_id γ 2 (by simp)).norm.const_mul C)
  have hFL (p) : MemLp (F p) 2 γ := hGB.mono'
    ((hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hFB p g)
  have hFp (g : E) : Continuous (fun p => F p g) := by
    have hp : Continuous (fun p => vectorPartition ρ (W p) V g) := by
      apply continuous_of_dominated (bound := fun _ => Real.exp (K+C*‖g‖))
      · intro p; exact (vectorPartition_integrable ρ (hWm' p) hVm (hW p) hV g).aestronglyMeasurable
      · intro p; apply ae_of_all; intro s
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (vectorEnergy_bound (hW p) hV g s))
      · exact integrable_const _
      · exact ae_of_all _ fun s => ((hWc s).add continuous_const).rexp
    exact hp.log (fun p => (vectorPartition_pos ρ (hWm' p) hVm (hW p) hV g).ne')
  have hAc : Continuous (fun p => ∫ g, F p g ∂γ) := by
    apply continuous_of_dominated (bound := fun g => K+C*‖g‖)
    · intro p; exact (hFL p).aestronglyMeasurable
    · intro p; exact ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hFB p g
    · exact hGB.integrable (by norm_num)
    · exact ae_of_all _ hFp
  have hAB (p) : |∫ g, F p g ∂γ| ≤ ∫ g, (K+C*‖g‖) ∂γ := by
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono (hFL p |>.integrable (by norm_num) |>.norm)
        (hGB.integrable (by norm_num)) (fun g => by simpa only [Real.norm_eq_abs] using hFB p g))
  have hAL : MemLp (fun p => ∫ g, F p g ∂γ) 2 ν :=
    MemLp.of_bound hAc.aestronglyMeasurable _ (ae_of_all _ hAB)
  apply variance_prod_le_memLp ν γ
    ((hGB.comp_snd ν).mono' hFm.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,Function.uncurry] using hFB p.1 p.2)) hFL hAL
  · intro p
    exact vectorLogPartition_gaussian_variance ρ (hWm' p) hVm hC (hW p) hV
  · apply variance_pi_le_of_bounded_differences μ n hAc hAB
    intro p i z
    rw [← integral_sub ((hFL _).integrable (by norm_num)) ((hFL _).integrable (by norm_num))]
    have hh := norm_integral_le_of_norm_le_const (μ := γ)
      (f := fun g => F (Function.update p i z) g-F p g) (C := c)
      (ae_of_all _ fun g => by
        simpa only [Real.norm_eq_abs] using vectorLogPartition_data_bound ρ
          (hWm' _) (hWm' _) hVm (hW _) (hW _) hV (hosc p i z) g)
    simpa using hh

end MixedRoot
end SphericalPerceptron

end
end
end

end OAI
