import OAI.Geometry.RCD.Heat.KernelHeatL2Representation

namespace OAI

/-! # Approximating the bounded complement in the conservative heat kernel

The complement of an L2 function need not be in L2 on an infinite-volume
space. Finite-ball truncations stay in L2 and their heat values converge
to the exact bounded complement, by mass conservation.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ Q ker)

include hk in
theorem bounded_heat_complement_sequence (p : X) (f : Lp ℝ 2 μ) (A : ℝ≥0)
    (hf0 : 0 ≤ f) (hfA : ∀ᵐ x ∂μ, |f x| ≤ A) :
    ∃ g : ℕ → Lp ℝ 2 μ,
      (∀ k, 0 ≤ g k) ∧ (∀ k, ∀ᵐ x ∂μ, |g k x| ≤ A) ∧
      ∀ (t : ℝ), 0 < t → ∀ x : X,
        Tendsto (fun k => kernelHeat μ Q hk t (g k) x) atTop
          (𝓝 ((A:ℝ)-kernelHeat μ Q hk t f x)) := by
  let E (k : ℕ) := closedBall p ((k:ℝ)+1)
  have hE (k : ℕ) : MeasurableSet (E k) := measurableSet_closedBall
  let F (k : ℕ) := (E k).indicator (fun x => (A:ℝ)-f x)
  have hm (k : ℕ) : MemLp (F k) 2 μ := by
    have hconst : MemLp ((E k).indicator (fun _ : X => (A:ℝ))) 2 μ :=
      memLp_indicator_const 2 (hE k) _ (Or.inr (isCompact_closedBall p ((k:ℝ)+1)).measure_lt_top.ne)
    have he : F k = (E k).indicator (fun _ : X => (A:ℝ))-(E k).indicator (fun x => f x) := by
      ext x
      by_cases hx : x ∈ E k <;> simp [F,indicator_of_mem,indicator_of_notMem,hx]
    rw [he]
    exact hconst.sub ((Lp.memLp f).indicator (hE k))
  let g (k : ℕ) := (hm k).toLp (F k)
  have hg (k : ℕ) : g k =ᵐ[μ] F k := (hm k).coeFn_toLp
  have hb (k : ℕ) : ∀ᵐ x ∂μ, 0 ≤ F k x ∧ F k x ≤ A := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfA] with x h0 hA
    by_cases hx : x ∈ E k
    · rw [show F k x=(A:ℝ)-f x from indicator_of_mem hx _]
      exact ⟨sub_nonneg.mpr ((le_abs_self _).trans hA),sub_le_self _ h0⟩
    · simp only [F,indicator_of_notMem hx]
      exact ⟨le_rfl,A.coe_nonneg⟩
  refine ⟨g,?_,?_,?_⟩
  · intro k
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hg k,hb k] with x he hx
    rw [he]
    exact hx.1
  · intro k
    filter_upwards [hg k,hb k] with x he hx
    rw [he,abs_of_nonneg hx.1]
    exact hx.2
  · intro t ht x
    have hi : Integrable (fun y => ker t x y*(A:ℝ)) μ := (hk.integrable t ht x).mul_const A
    have hmeas (k : ℕ) : AEStronglyMeasurable (fun y => ker t x y*F k y) μ :=
      (hk.continuous_right t ht x).aestronglyMeasurable.mul (hm k).aestronglyMeasurable
    have hbound (k : ℕ) : ∀ᵐ y ∂μ, ‖ker t x y*F k y‖ ≤ ker t x y*(A:ℝ) := by
      filter_upwards [hb k] with y hy
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hk.nonneg t ht x y) hy.1)]
      exact mul_le_mul_of_nonneg_left hy.2 (hk.nonneg t ht x y)
    have hconv : ∀ᵐ y ∂μ, Tendsto (fun k => ker t x y*F k y) atTop
        (𝓝 (ker t x y*((A:ℝ)-f y))) := by
      apply Eventually.of_forall
      intro y
      obtain ⟨N,hN⟩ := exists_nat_gt (dist y p)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with k hk
      have hy : y ∈ E k := by
        change dist y p ≤ (k:ℝ)+1
        have hn : (N:ℝ) ≤ k := by exact_mod_cast hk
        linarith
      rw [show F k y=(A:ℝ)-f y from indicator_of_mem hy _]
    have hlim := tendsto_integral_of_dominated_convergence
      (fun y => ker t x y*(A:ℝ)) hmeas hi hbound hconv
    have hprod : Integrable (fun y => ker t x y*f y) μ := by
      have hh := (hk.integrable t ht x).bdd_mul (Lp.aestronglyMeasurable f)
        (by simpa only [Real.norm_eq_abs] using hfA)
      simpa only [mul_comm] using hh
    have he : (∫ y, ker t x y*((A:ℝ)-f y) ∂μ) = (A:ℝ)-kernelHeat μ Q hk t f x := by
      simp_rw [mul_sub]
      rw [integral_sub hi hprod,integral_mul_const,hk.mass_one t ht x,one_mul,
        kernelHeat_eq_integral μ Q hk ht f x]
    rw [he] at hlim
    apply hlim.congr'
    apply Eventually.of_forall
    intro k
    dsimp only
    rw [kernelHeat_eq_integral μ Q hk ht]
    exact integral_congr_ae ((hg k).mono fun y hy => congrArg (fun z : ℝ => ker t x y*z) hy.symm)

end RegularPointCoordinates

end

end OAI
