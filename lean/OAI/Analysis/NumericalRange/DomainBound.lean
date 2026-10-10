import OAI.Analysis.NumericalRange.MetricNorm

namespace OAI

universe u_259

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n m : ℕ} [Nonempty (Fin n)]

theorem exists_two_similarity (A : Matrix (Fin n) (Fin n) ℂ)
    (hW : numericalRange A ⊆ D.domain) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, IsUnit S ∧ ‖S‖ * ‖S⁻¹‖ ≤ 2 ∧
      (S*matrixAnalyticEval A D.interior.toDisk*S⁻¹)ᴴ *
        (S*matrixAnalyticEval A D.interior.toDisk*S⁻¹) ≤ 1 := by
  have hA : spectrum ℂ A ⊆ D.domain := (spectrum_subset_numericalRange A).trans hW
  let T := matrixAnalyticEval A D.interior.toDisk
  have hT : spectralRadius ℂ T < 1 := D.coordinate_stable A hA
  obtain ⟨τ,H,hf,hp,hm,hext⟩ := exists_optimal_analytic_extremal hT
  let S := CFC.sqrt H
  have hu : IsUnit S := metric_sqrt_isUnit hp
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian
  have hc : (S*T*S⁻¹)ᴴ*(S*T*S⁻¹) ≤ 1 :=
    (matrix_contractivity_iff _).mpr (metric_similarity_contraction hf hp)
  have ha : Real.sqrt τ ≤ 2 := by
    by_cases hτ : τ ≤ 1
    · have hs : Real.sqrt τ ≤ 1 := by
        calc Real.sqrt τ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hτ
             _ = 1 := Real.sqrt_one
      exact hs.trans (by norm_num)
    · have ht : 1 < τ := lt_of_not_ge hτ
      have ha0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr (zero_lt_one.trans ht)
      obtain ⟨X,Y,F,hx,hy,hX,hY,hXY,hF,hn,he⟩ := hext ht
      have hX' : S*X = (Real.sqrt τ:ℂ) • X := by
        simpa only [Complex.coe_smul] using hX
      have hA' : spectrum ℂ (S*A*S⁻¹) ⊆ D.domain := by rwa [spectrum_matrix_similarity hu]
      have hc' : (matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk)ᴴ *
          matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk ≤ 1 := by
        rwa [matrixAnalyticEval_similarity hu]
      have hFa : AnalyticOnNhd ℂ (fun z => F (D.interior.toDisk z)) (closure D.domain) := by
        intro z hz
        exact (hF _ (D.interior.closure_maps hz)).comp
          (D.interior.analytic_to z (D.interior.closure_subset hz))
      have hFn : ∀ z ∈ closure D.domain, ‖F (D.interior.toDisk z)‖ ≤ 1 :=
        fun z hz => hn _ (D.interior.closure_maps hz)
      have hFe : Matrix.toEuclideanCLM (n := Fin n × Fin n) (𝕜 := ℂ)
          (completeAnalyticEval (S*A*S⁻¹) (fun z => F (D.interior.toDisk z)))
          (vectorize X) = vectorize Y := by
        rw [completeAnalyticEval_comp (S*A*S⁻¹) (D.coordinate_analytic_spectrum _ hA')
          (fun i j z hz => matrix_entry_analytic (hF _ (ball_subset_closedBall (D.toDisk_maps (hA' hz)))) i j),
          matrixAnalyticEval_similarity hu]
        exact he
      exact D.extremal_condition_bound A hW hS hu hc' ha0 hX' hY hx hy hXY hFa hFn hFe
  exact ⟨S,hu,(metric_condition_estimate hf hp).trans ha,hc⟩

theorem polynomial_bound_unit {ι : Type u_259} (s : Finset ι)
    (A : Matrix (Fin n) (Fin n) ℂ) (B : ι → Matrix (Fin m) (Fin m) ℂ) (p : ι → ℕ)
    (hW : numericalRange A ⊆ D.domain)
    (hn : ∀ z ∈ closure D.domain, ‖∑ k ∈ s, z^(p k) • B k‖ ≤ 1) :
    ‖∑ k ∈ s, (A^(p k)) ⊗ₖ B k‖ ≤ 2 := by
  have hA : spectrum ℂ A ⊆ D.domain := (spectrum_subset_numericalRange A).trans hW
  obtain ⟨S,hu,hs,hc⟩ := D.exists_two_similarity A hW
  have hD : spectralRadius ℂ (S*matrixAnalyticEval A D.interior.toDisk*S⁻¹) < 1 := by
    simpa only [spectralRadius_eq_of_unital, spectrum_matrix_similarity hu]
      using D.coordinate_stable A hA
  refine (coordinate_polynomial_similarity_bound s A S B p hu D.isOpen hA
    (D.coordinate_analytic_spectrum A hA) (fun z hz => ball_subset_closedBall (D.toDisk_maps (hA hz)))
    (D.interior.analytic_from.mono D.interior.closedDisk_subset)
    (fun z hz => D.interior.left_inverse z (D.interior.closure_subset (subset_closure hz))) hD hc ?_).trans hs
  intro t
  apply hn
  have ht : fourier 1 t ∈ sphere (0:ℂ) 1 := mem_sphere_zero_iff_norm.mpr (by simpa only [fourier_one] using Circle.norm_coe t.toCircle)
  exact frontier_subset_closure
    (D.interior.inverse_sphere_frontier D.isOpen ▸ mem_image_of_mem D.interior.fromDisk ht)
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
