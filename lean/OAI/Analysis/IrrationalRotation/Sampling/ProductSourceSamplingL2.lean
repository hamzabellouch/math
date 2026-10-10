import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeightAssembly
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingIdealBounds
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTestAlmostSure
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingUniformL2

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel.SamplingWeights

theorem memLp_orientedAverage (endpoint : Bool) (D I N : Finset ℕ)
    {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (q : ℝ≥0∞) :
    MemLp (orientedAverage endpoint D I N h α θ) q baseMeasure := by
  cases endpoint
  · have heq : orientedAverage false D I N h α θ =
        fun x => (N.card : ℝ)⁻¹ * ∑ n ∈ N, orbitWeight D I h α θ n x := by
      funext x
      exact orientedAverage_first D I N h α θ x
    rw [heq]
    exact (memLp_finsetSum N (fun n _ => memLp_orbitWeight D I hh hα θ n q)).const_mul _
  · have heq : orientedAverage true D I N h α θ = fun y =>
        (N.card : ℝ)⁻¹ * ∑ n ∈ N,
          orbitWeight D I h α θ n (rotationIterate θ (-(n : ℤ)) y) := by
      funext y
      exact orientedAverage_second D I N h α θ y
    rw [heq]
    exact (memLp_finsetSum N (fun n _ =>
      (memLp_orbitWeight D I hh hα θ n q).comp_measurePreserving
        (ProductCocycle.measurePreserving_rotate θ (-(n : ℤ))))).const_mul _

theorem sourceTestedError_univ_eq (p : ProductScaleData) (N : ℕ → Finset ℕ)
    (endpoint : Bool) (I : Finset ℕ) (j : ℕ) (θ : ℕ → ℝ) (x : Base) :
    sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ) j θ x =
      orientedAverage endpoint (Finset.range (p.prefixCount (j + 1))) I (N j)
        ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) θ x -
      idealProduct endpoint (Finset.range (p.prefixCount (j + 1))) I
        ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2)
        (fun _ => univ) (fun _ => univ) x := rfl

theorem source_orientedAverage_uniform_bound
    {p : ProductScaleData} (hp : ProductScaleLaws p) (N : ℕ → Finset ℕ)
    (θ : ℕ → ℝ) (I : Finset ℕ)
    (herr : ∀ endpoint : Bool, Tendsto (fun j => ∫ x,
      (sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ) j θ x)^2
        ∂baseMeasure) atTop (𝓝 0)) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ endpoint : Bool, ∀ j : ℕ,
      eLpNorm (orientedAverage endpoint (Finset.range (p.prefixCount (j + 1))) I
        (N j) ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) θ)
        2 baseMeasure ≤ ENNReal.ofReal H := by
  let f (endpoint : Bool) (j : ℕ) :=
    orientedAverage endpoint (Finset.range (p.prefixCount (j + 1))) I (N j)
      ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) θ
  let z (endpoint : Bool) (j : ℕ) :=
    idealProduct endpoint (Finset.range (p.prefixCount (j + 1))) I
      ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2)
      (fun _ => univ) (fun _ => univ)
  have hm (j : ℕ) : 0 < (p.m j : ℝ) := by exact_mod_cast hp.m_pos j
  have hh (j : ℕ) : 0 < (p.m j : ℝ)^(-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos (hm j) _
  have hα (j : ℕ) : 0 < 1 / (p.m j : ℝ)^2 := one_div_pos.mpr (pow_pos (hm j) 2)
  have hf (endpoint : Bool) (j : ℕ) : MemLp (f endpoint j) 2 baseMeasure :=
    memLp_orientedAverage endpoint _ I (N j) (hh j) (hα j) θ 2
  have hz (endpoint : Bool) (j : ℕ) : MemLp (z endpoint j) 2 baseMeasure :=
    memLp_idealProduct endpoint _ I (hh j) (hα j) _ _
      (fun _ => MeasurableSet.univ) (fun _ => MeasurableSet.univ)
  obtain ⟨B, hB, hbound⟩ := source_idealProduct_uniform_bound hp
  have hone (endpoint : Bool) : ∃ H : ℝ, 0 ≤ H ∧ ∀ j,
      eLpNorm (f endpoint j) 2 baseMeasure ≤ ENNReal.ofReal H := by
    have hzbound (j : ℕ) : ‖(hz endpoint j).toLp (z endpoint j)‖ ≤ B := by
      rw [Lp.norm_toLp]
      have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (hbound j endpoint I (fun _ => univ) (fun _ => univ)
          (fun _ => MeasurableSet.univ) (fun _ => MeasurableSet.univ))
      simpa only [ENNReal.toReal_ofReal hB] using hb
    have he : Tendsto (fun j => ∫ x, (f endpoint j x - z endpoint j x)^2
        ∂baseMeasure) atTop (𝓝 0) := by
      simpa only [sourceTestedError_univ_eq] using herr endpoint
    have hlim := ProductSampling.tendsto_norm_toLp_sub_of_integral_sq
      (f endpoint) (z endpoint) (hf endpoint) (hz endpoint) he
    obtain ⟨H, hH, hb⟩ := ProductSampling.exists_uniform_norm_bound_of_error_tendsto
      (fun j => (hf endpoint j).toLp (f endpoint j))
      (fun j => (hz endpoint j).toLp (z endpoint j)) hzbound hlim
    refine ⟨H, hH, fun j => ?_⟩
    rw [← ENNReal.ofReal_toReal (hf endpoint j).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Lp.norm_toLp] using hb j)
  obtain ⟨Hf, hHf, hfirst⟩ := hone false
  obtain ⟨Hg, hHg, hsecond⟩ := hone true
  refine ⟨max Hf Hg, hHf.trans (le_max_left _ _), ?_⟩
  intro endpoint j
  cases endpoint
  · exact (hfirst j).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact (hsecond j).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))

theorem source_hasUniformL2Marginals_of_energy_convergence
    {p : ProductScaleData} (hp : ProductScaleLaws p) (N : ℕ → Finset ℕ)
    (θ : ℕ → ℝ) (I : Finset ℕ)
    (herr : ∀ endpoint : Bool, Tendsto (fun j => ∫ x,
      (sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ) j θ x)^2
        ∂baseMeasure) atTop (𝓝 0)) :
    HasUniformL2Marginals (fun j => TailTrimming.orbitAverageMeasure θ (N j)
      (fun n x => ENNReal.ofReal (orbitWeight (Finset.range (p.prefixCount (j + 1))) I
        ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) θ n x))) := by
  obtain ⟨H, hH, hb⟩ := source_orientedAverage_uniform_bound hp N θ I herr
  apply hasUniformL2Marginals_of_oriented_bounds θ I
    (fun j => Finset.range (p.prefixCount (j + 1))) N
    (fun j => (p.m j : ℝ)^(-(3 / 5 : ℝ))) (fun j => 1 / (p.m j : ℝ)^2)
    (fun j => Real.rpow_pos_of_pos (by exact_mod_cast hp.m_pos j) _) ?_ hH
    (hb false) (hb true)
  intro j
  have hm : 0 < (p.m j : ℝ) := by exact_mod_cast hp.m_pos j
  positivity

end Invariant233.ProductModel.SamplingWeights

end

end OAI
