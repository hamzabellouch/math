import OAI.Analysis.NumericalRange.DensityIdentification

namespace OAI

noncomputable section

universe u_253 u_254

namespace CompleteCrouzeix
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace AdmissibleDomain

section
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {n : Type u_253} {m : Type u_254} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype m] [DecidableEq m]
lemma coordinate_analytic_spectrum (D : AdmissibleDomain)
    {n : Type u_253} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ D.interior.toDisk z :=
  fun z hz => D.interior.analytic_to z (D.interior.closure_subset (subset_closure (hA hz)))
lemma coordinate_stable (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    spectralRadius ℂ (matrixAnalyticEval A D.interior.toDisk) < 1 :=
  matrixAnalyticEval_stable A (D.coordinate_analytic_spectrum A hA)
    (fun _z hz => mem_ball_zero_iff.mp (D.toDisk_maps (hA hz)))
def positiveDensity (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    C(UnitAddCircle,Matrix n n ℂ) :=
  ⟨pulledDiskDensity (matrixAnalyticEval A D.interior.toDisk) D.ψ,
    pulledDiskDensity_continuous (D.coordinate_stable A hA) D.ψ_analytic (fun _ ht => D.ψ_boundary ht)⟩
lemma positiveDensity_nonneg (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ * matrixAnalyticEval A D.interior.toDisk ≤ 1)
    (t : UnitAddCircle) : 0 ≤ D.positiveDensity A hA t :=
  pulledDiskDensity_nonneg (D.coordinate_stable A hA) hc
    (fun _ ht => D.ψ_boundary ht) (fun _ ht => D.ψ_jacobian ht) t
lemma positiveDensity_mass (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    (∫ t, D.positiveDensity A hA t ∂AddCircle.haarAddCircle) = 1 :=
  pulledDiskDensity_mass (D.coordinate_stable A hA) D.ψ_analytic
    (fun _ ht => D.ψ_boundary ht) (fun _ hz => D.ψ_mass hz)
lemma positiveDensity_representation (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {v : ℂ → Matrix m m ℂ} (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    completeAnalyticEval A v = ∫ t, D.positiveDensity A hA t ⊗ₖ D.trace v hv t
      ∂AddCircle.haarAddCircle := D.positive_representation A hA hv
lemma positiveDensity_operator_representation (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {v : ℂ → Matrix m m ℂ} (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (completeAnalyticEval A v) =
      ∫ t, Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)
        (D.positiveDensity A hA t ⊗ₖ D.trace v hv t) ∂AddCircle.haarAddCircle := by
  let e : Matrix (n × m) (n × m) ℂ →L[ℂ] _ :=
    (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
  have hi := (continuous_kron (D.positiveDensity A hA).continuous (D.trace v hv).continuous).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  rw [D.positiveDensity_representation A hA hv]
  have : CompleteSpace (EuclideanSpace ℂ (n × m)) := inferInstance
  have : CompleteSpace (EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
    ContinuousLinearMap.instCompleteSpace
  exact (e.integral_comp_comm hi).symm
end
variable (D : AdmissibleDomain) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
lemma resolventField_posSemidef (hW : numericalRange A ⊆ D.domain) (t : UnitAddCircle) :
    (D.resolventField A t+(D.resolventField A t)ᴴ).PosSemidef := by
  apply supporting_resolvent_posSemidef
  · intro hz
    exact D.G_ne_interior (hW hz) (Circle.norm_coe t.toCircle).ge rfl
  · intro w hw
    exact D.support _ t.toCircle.2 w (subset_closure (hW hw))
end AdmissibleDomain
end CompleteCrouzeix

end

end OAI
