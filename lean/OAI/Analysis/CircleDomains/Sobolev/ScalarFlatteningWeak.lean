import OAI.Analysis.CircleDomains.Sobolev.ScalarFlatteningApproximation
import OAI.Analysis.CircleDomains.Sobolev.LocalBoundedSobolevChain

namespace OAI

/-! Distributional chain rule for the constructed flattening map. Smooth
primitives converge with their bounded derivative multipliers, so the
identity follows from the smooth chain rule. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem flattenValues_weak_partial
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ p ∈ U, u p ∈ Icc (-B) B)
    {O : Set ℝ} (hO : IsOpen O) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun p => Oᶜ.indicator (fun _ => (1 : ℝ)) (u p) * W.weakGrad p i)
      (flattenValues O ∘ u) U := by
  obtain ⟨F, hF, hlim, hd, hdlim⟩ := exists_flattenValues_smooth_approximation hO
  intro φ hφ hs hsub
  let dφ : EuclideanPlane → ℝ := fun p => fderiv ℝ φ p (EuclideanSpace.single i 1)
  have hdc : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport dφ := hs.fderiv_apply (𝕜 := ℝ) _
  have hFbound (n : ℕ) (p : EuclideanPlane) : ‖F n (u p)‖ ≤ ‖u p‖ := by
    have h := (hF n).2.2.dist_le_mul (u p) 0
    simpa only [(hF n).2.1, dist_zero_right, NNReal.coe_one, one_mul] using h
  have hleft : Tendsto (fun n => ∫ p in U, F n (u p)*dφ p) atTop
      (𝓝 (∫ p in U, flattenValues O (u p)*dφ p)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun p => B*‖dφ p‖)
    · intro n
      exact (((hF n).1.continuous.comp hu).aestronglyMeasurable).mul hdc.aestronglyMeasurable
    · exact ((hdc.integrable_of_hasCompactSupport hds).norm.const_mul B).restrict
    · intro n
      filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hFbound n p).trans
        (by simpa only [Real.norm_eq_abs] using abs_le.mpr (hb p hp))) (norm_nonneg _)
    · exact Eventually.of_forall fun p => (hlim (u p)).mul_const (dφ p)
  have hφL : MemLp φ 2 (volume.restrict U) :=
    (hφ.continuous.memLp_of_hasCompactSupport hs).restrict U
  have hgφ : Integrable (fun p => W.weakGrad p i*φ p) (volume.restrict U) :=
    (W.weakGrad_component_memLp i).integrable_mul
      hφL
  have hright : Tendsto (fun n => ∫ p in U, deriv (F n) (u p)*W.weakGrad p i*φ p) atTop
      (𝓝 (∫ p in U, Oᶜ.indicator (fun _ => (1 : ℝ)) (u p)*W.weakGrad p i*φ p)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun p => ‖W.weakGrad p i*φ p‖)
    · intro n
      exact ((((hF n).1.continuous_deriv le_rfl).comp hu).aestronglyMeasurable.mul
        (W.weakGrad_component_memLp i).aestronglyMeasurable).mul hφ.continuous.aestronglyMeasurable
    · exact hgφ.norm
    · intro n
      exact Eventually.of_forall fun p => by
        rw [mul_assoc, norm_mul]
        exact (mul_le_mul_of_nonneg_right (by
          rw [Real.norm_eq_abs, abs_of_nonneg (hd n (u p)).1]
          exact (hd n (u p)).2) (norm_nonneg _)).trans_eq (one_mul _)
    · exact Eventually.of_forall fun p => ((hdlim (u p)).mul_const (W.weakGrad p i)).mul_const (φ p)
  have heq (n : ℕ) : (∫ p in U, F n (u p)*dφ p) =
      -(∫ p in U, deriv (F n) (u p)*W.weakGrad p i*φ p) := by
    simpa only [comp_apply, dφ] using
      bounded_sobolev_chain_rule_on_symmetric hU W hB hb (hF n).1 i φ hφ hs hsub
  exact tendsto_nhds_unique hleft (by simpa only [heq] using hright.neg)

end CircleDomainRigidity

end

end OAI
