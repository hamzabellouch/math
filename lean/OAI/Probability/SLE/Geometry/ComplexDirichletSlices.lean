import OAI.Probability.SLE.Geometry.ComplexAngularEnergy

namespace OAI

/-! Finite holomorphic energy gives square-integrable derivatives and
low-energy angular sections in each unit logarithmic strip. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

lemma deriv_memLp_two_of_energy {f : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hf : DifferentiableOn ℂ f S)
    (he : (∫⁻ z in S, ENNReal.ofReal (‖deriv f z‖^2))<∞) :
    MemLp (deriv f) 2 (volume.restrict S) := by
  have hc : ContinuousOn (deriv f) S := (hf.deriv hS).continuousOn
  have hm : AEStronglyMeasurable (deriv f) (volume.restrict S) :=
    hc.aestronglyMeasurable hS.measurableSet
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  exact ⟨hm.norm.pow 2, (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ (fun _ => sq_nonneg _))).mpr he⟩

lemma exists_complex_energy_section (g : ℝ × ℝ → ℂ) (q : ℝ)
    (hg : MemLp g 2 ((volume.restrict (Ioo q (q+1))).prod
      (volume.restrict (Ioo 0 Real.pi)))) :
    ∃ v∈Ioo q (q+1), MemLp (fun θ => g (v,θ)) 2 (volume.restrict (Ioo 0 Real.pi)) ∧
      (∫ θ in Ioo 0 Real.pi, ‖g (v,θ)‖^2) ≤
        ∫ p, ‖g p‖^2 ∂((volume.restrict (Ioo q (q+1))).prod (volume.restrict (Ioo 0 Real.pi))) := by
  let J := Ioo q (q+1)
  let K := Ioo (0:ℝ) Real.pi
  have hi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hgood : ∀ᵐ v ∂volume.restrict J,
      v∈J ∧ MemLp (fun θ => g (v,θ)) 2 (volume.restrict K) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,hi.prod_right_ae,
      hg.aestronglyMeasurable.prodMk_left] with v hv hvi hvm
    exact ⟨hv,(memLp_two_iff_integrable_sq_norm hvm).mpr hvi⟩
  have : IsProbabilityMeasure (volume.restrict J) := by
    constructor
    simp [J,Real.volume_Ioo]
  let energy := fun v => ∫ θ in K, ‖g (v,θ)‖^2
  have hei : Integrable energy (volume.restrict J) := hi.integral_prod_left
  let Good := fun v => v∈J ∧ MemLp (fun θ => g (v,θ)) 2 (volume.restrict K)
  have hnull : (volume.restrict J) {v | ¬Good v}=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hgood] with v hv
    exact fun h => h hv
  obtain ⟨v,hv,hve⟩ := exists_notMem_null_le_integral hei hnull
  have hv' : Good v := not_not.mp hv
  refine ⟨v,hv'.1,hv'.2,?_⟩
  rw [integral_prod _ hi]
  exact hve

end SLEExactGauge

end

end OAI
