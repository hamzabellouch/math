import OAI.Analysis.CircleDomains.Rigidity.ConductivityContraction

namespace OAI

/-! The actual two-valued conductivity coefficient. Its strict contraction
constant is (n-1)/(n+1), and the constructed density vanishes off F. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

def conductivityRatio (n : ℕ) (hn : 1 ≤ n) : ℝ≥0 :=
  ⟨((n : ℝ) - 1) / ((n : ℝ) + 1), div_nonneg (by
    have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith) (by positivity)⟩

def conductivityCoefficient (F : Set EuclideanPlane) (n : ℕ) (x : EuclideanPlane) : ℝ :=
  F.indicator (fun _ => ((n : ℝ) - 1) / ((n : ℝ) + 1)) x

 theorem conductivityRatio_lt_one (n : ℕ) (hn : 1 ≤ n) : conductivityRatio n hn < 1 := by
  change ((n : ℝ) - 1) / ((n : ℝ) + 1) < 1
  apply (div_lt_one (by positivity)).mpr
  linarith

 theorem conductivityCoefficient_memLp {F : Set EuclideanPlane} (hF : IsCompact F) (n : ℕ) :
    MemLp (conductivityCoefficient F n) 2 volume :=
  memLp_indicator_const 2 hF.measurableSet _ (Or.inr hF.measure_lt_top.ne)

 theorem conductivityCoefficient_bound (F : Set EuclideanPlane) (n : ℕ) (hn : 1 ≤ n) :
    ∀ x, ‖conductivityCoefficient F n x‖ ≤ conductivityRatio n hn := by
  intro x
  by_cases hx : x ∈ F
  · simp only [conductivityCoefficient, indicator_of_mem hx, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (conductivityRatio n hn).2)
  · simp only [conductivityCoefficient, indicator_of_notMem hx, norm_zero]
    exact (conductivityRatio n hn).2

 theorem exists_compact_conductivity_density {F : Set EuclideanPlane} (hF : IsCompact F)
    (n : ℕ) (hn : 1 ≤ n) (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2)
    (hS : ∀ f, ‖S f‖ ≤ ‖f‖) :
    ∃ g : ComplexPlaneL2,
      (∀ᵐ x ∂volume, g x = (conductivityCoefficient F n x : ℂ) * star (1 + S g x)) ∧
      (∀ᵐ x ∂volume, x ∉ F → g x = 0) := by
  obtain ⟨g, hg, _⟩ := exists_conductivity_density (conductivityCoefficient F n)
    (conductivityCoefficient_memLp hF n) (conductivityRatio n hn)
    (conductivityRatio_lt_one n hn)
    (Eventually.of_forall (conductivityCoefficient_bound F n hn)) S hS
  exact ⟨g, hg, conductivity_density_support hg (fun x hx => indicator_of_notMem hx _)⟩

end CircleDomainRigidity

end

end OAI
