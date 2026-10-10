import OAI.Probability.GaussianRegression.ReplicaMoments
import OAI.Probability.GaussianRegression.GaussianKernel

namespace OAI

/-!
Projection smoothing, Gaussian noise, and bounds under weak limits.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def projectionSmoothing (ν : Measure E) (φ : ℝ → ℝ≥0∞) (m : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) : ℝ≥0∞ :=
  ∫⁻ t, ∏ j, φ (z.2 j - ⟪t, z.1 j⟫) ∂ν

lemma measurable_projectionSmoothing (ν : Measure E) [SFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m : ℕ) :
    Measurable (projectionSmoothing ν φ m) := by
  apply Measurable.lintegral_prod_right
  fun_prop

lemma projectionSmoothing_pow (ν : Measure E) [SigmaFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m n : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) :
    (projectionSmoothing ν φ m z)^(n+1) =
      ∫⁻ w : E × (Fin n → E),
        (∏ j, φ (z.2 j - ⟪w.1, z.1 j⟫)) *
          ∏ i, ∏ j, φ (z.2 j - ⟪w.2 i, z.1 j⟫)
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
  rw [lintegral_prod _ (by fun_prop)]
  have hG : Measurable (fun v : Fin n → E =>
      ∏ i, ∏ j, φ (z.2 j - ⟪v i, z.1 j⟫)) := by fun_prop
  simp_rw [lintegral_const_mul _ hG]
  rw [lintegral_mul_const _ (by fun_prop), ← lintegral_pow_pi ν
    (fun t : E => ∏ j, φ (z.2 j - ⟪t, z.1 j⟫)) (by fun_prop) n]
  exact pow_succ' _ _

theorem projectionSmoothing_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × (Fin m → ℝ),
      (projectionSmoothing ν φ m z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
       ν Set.univ * (replicaConstant ν a m)^n := by
  simp_rw [projectionSmoothing_pow ν φ hφ m n]
  rw [lintegral_lintegral_swap (by fun_prop), lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ p, ∫⁻ v : Fin n → E, replicaWeight m p v
        ∂Measure.pi (fun _ => ν) ∂ν := by
      apply lintegral_mono
      intro p
      apply lintegral_mono_ae
      filter_upwards [ae_replica_linearIndependent hν hsupport p n
        (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg m)) hmargin)] with v hv
      rw [lintegral_prod _ (by fun_prop), replicaWeight_eq_det, sqrt_det_gram]
      exact gaussian_replica_kernel_bound p v hv φ hφ hφ1 m
    _ ≤ ∫⁻ _p, (replicaConstant ν a m)^n ∂ν :=
      lintegral_mono fun p => replica_integral_bound hν hsupport m p n hmargin
    _ = _ := by rw [lintegral_const, mul_comm]
end SmoothingMoments

section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma measure_pi_withDensity (n : ℕ) (f : Fin n → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i)) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he (x : Fin n → X) :
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x =
        ∏ i, (s i).indicator (f i) (x i) := by
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ s i := by simpa only [Set.mem_univ_pi, not_forall] using hx
      obtain ⟨i, hi⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [he]
  rw [lintegral_fin_prod μ n _ (fun i => (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]
end ProductDensity

lemma pi_gaussian_map_scale (m : ℕ) (δ : ℝ) :
    (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
      (fun u => fun j => δ * u j) =
      Measure.pi (fun _ : Fin m => gaussianReal 0 (NNReal.mk (δ^2) (sq_nonneg δ))) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : ℝ => δ * x)
    (fun _ => (by fun_prop : Measurable (fun x : ℝ => δ * x)).aemeasurable)]
  simp_rw [gaussianReal_map_const_mul, mul_zero, mul_one]

lemma pi_gaussian_withDensity (m : ℕ) (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 v) =
      (volume : Measure (Fin m → ℝ)).withDensity (fun y => ∏ j, gaussianPDF 0 v (y j)) := by
  simp_rw [gaussianReal_of_var_ne_zero _ hv]
  have : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  rw [measure_pi_withDensity (volume : Measure ℝ) m
    (fun _ => gaussianPDF 0 v) (fun _ => measurable_gaussianPDF 0 v)]
  rfl
lemma lintegral_gaussian_shift_scale (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0)
    (a : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
      ∂Measure.pi (fun _ => gaussianReal 0 1) =
    ∫⁻ y : Fin m → ℝ, (∏ j, gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ)) (y j - a j)) * f y := by
  let v : ℝ≥0 := NNReal.mk (δ^2) (sq_nonneg δ)
  have hv : v ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  have he :
      (∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫⁻ y : Fin m → ℝ, f (a + y) ∂Measure.pi (fun _ => gaussianReal 0 v) := by
    rw [← pi_gaussian_map_scale m δ, lintegral_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he, pi_gaussian_withDensity m v hv,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hh (y : Fin m → ℝ) :
      (∏ j, gaussianPDF 0 v (y j)) * f (a + y) =
      (fun z : Fin m → ℝ => (∏ j, gaussianPDF 0 v (z j - a j)) * f z) (a + y) := by
    simp only [Pi.add_apply, add_sub_cancel_left]
  exact (lintegral_congr (μ := volume) hh).trans (lintegral_add_left_eq_self
    (μ := volume) (fun z : Fin m → ℝ => (∏ j, gaussianPDF 0 v (z j - a j)) * f z) a)

section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma withDensity_apply_le_moment (f : X → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∫⁻ x, f x ^ p ∂μ ≤ C) (S : Set X) (hS : MeasurableSet S) :
    μ.withDensity f S ≤ C^(1/p) * (μ S)^(1 - 1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) hpq
    hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have he : 1 / (Real.conjExponent p) = 1 - 1/p := by
    have hh := hpq.inv_add_inv_eq_one
    simpa only [one_div] using (eq_sub_of_add_eq' hh)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul, he] at h
  rw [withDensity_apply _ hS]
  exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow
    ((lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans hC) (by positivity)) le_rfl)
end HolderSet

section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

lemma map_apply_open_le_of_tendsto (F : X → Y) (Fₖ : ℕ → X → Y)
    (hF : Measurable F) (hFₖ : ∀ k, Measurable (Fₖ k))
    (ht : ∀ x, Tendsto (fun k => Fₖ k x) atTop (𝓝 (F x)))
    (C : ℝ≥0∞) (α : ℝ)
    (hbound : ∀ k U, IsOpen U → (ρ.map (Fₖ k)) U ≤ C * (τ U)^α)
    (U : Set Y) (hU : IsOpen U) :
    (ρ.map F) U ≤ C * (τ U)^α := by
  let f : ℕ → X → ℝ≥0∞ := fun k => (Fₖ k ⁻¹' U).indicator (fun _ => 1)
  have hf : ∀ k, Measurable (f k) := fun k =>
    measurable_const.indicator (hU.measurableSet.preimage (hFₖ k))
  have hind : ∀ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
      atTop.liminf (fun k => f k x) := by
    intro x
    by_cases hx : F x ∈ U
    · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' U from hx)]
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [(ht x).eventually (hU.mem_nhds hx)] with k hk
      change 1 ≤ (Fₖ k ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x
      rw [Set.indicator_of_mem (show x ∈ Fₖ k ⁻¹' U from hk)]
    · rw [Set.indicator_of_notMem (show x ∉ F ⁻¹' U from hx)]
      exact zero_le
  calc
    (ρ.map F) U = ∫⁻ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ρ := by
      rw [Measure.map_apply hF hU.measurableSet,
        lintegral_indicator (hU.measurableSet.preimage hF)]
      simp
    _ ≤ ∫⁻ x, atTop.liminf (fun k => f k x) ∂ρ := lintegral_mono hind
    _ ≤ atTop.liminf (fun k => ∫⁻ x, f k x ∂ρ) := lintegral_liminf_le hf
    _ ≤ _ := by
      apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      apply Filter.Eventually.frequently
      filter_upwards [] with k
      have hk := hbound k U hU
      simpa [f, lintegral_indicator (hU.measurableSet.preimage (hFₖ k)),
        Measure.map_apply (hFₖ k) hU.measurableSet] using hk
end LimitSet

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

lemma ennreal_rpow_iInf {ι : Sort*} (f : ι → ℝ≥0∞) {α : ℝ} (hα : 0 < α) :
    (⨅ i, f i)^α = ⨅ i, (f i)^α :=
  (ENNReal.orderIsoRpow α hα).map_iInf f

lemma measure_apply_le_of_isOpen (μ τ : Measure Y) [τ.OuterRegular]
    {C : ℝ≥0∞} (hC : C ≠ ∞) {α : ℝ} (hα : 0 < α)
    (hbound : ∀ U, IsOpen U → μ U ≤ C * (τ U)^α) (S : Set Y) :
    μ S ≤ C * (τ S)^α := by
  by_cases hC0 : C = 0
  · simp only [hC0, zero_mul] at hbound ⊢
    exact (measure_mono (Set.subset_univ S)).trans (hbound Set.univ isOpen_univ)
  rw [S.measure_eq_iInf_isOpen τ]
  simp_rw [ennreal_rpow_iInf _ hα, ENNReal.mul_iInf_of_ne hC0 hC]
  exact le_iInf fun U => le_iInf fun hSU => le_iInf fun hU =>
    (measure_mono hSU).trans (hbound U hU)

end NoiselessRegression

end

end OAI
