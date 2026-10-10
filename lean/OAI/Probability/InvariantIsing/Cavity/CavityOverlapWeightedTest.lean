import OAI.Probability.InvariantIsing.Cavity.CavityOriginalFullOverlap

namespace OAI

/-! A bounded continuous extension of the overlap-weighted test from
[-1,1], for the full original-model self-consistency identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BoundedContinuousFunction

namespace InvariantIsing

def cavityOverlapWeightedTest (Φ : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => Φ x * (Set.projIcc (-1) 1 (by norm_num) x : ℝ))
    (Φ.continuous.mul (continuous_subtype_val.comp (continuous_projIcc (h := (by norm_num : (-1 : ℝ) ≤ 1))))) ‖Φ‖
    (fun x => by
      rw [Real.norm_eq_abs,abs_mul]
      have hx : |(Set.projIcc (-1) 1 (by norm_num) x : ℝ)| ≤ 1 :=
        abs_le.mpr (Set.projIcc (-1) 1 (by norm_num) x).property
      exact (mul_le_mul (by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm x)
        hx (abs_nonneg _) (norm_nonneg Φ)).trans_eq (mul_one _))

lemma cavityOverlapWeightedTest_eq (Φ : ℝ →ᵇ ℝ) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    cavityOverlapWeightedTest Φ x = Φ x * x := by
  simp only [cavityOverlapWeightedTest,BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) hx]

lemma cavity_full_weighted_overlap_identity {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (θ : Measure (LabeledTree depth)) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (site : Fin N) :
    (∫ T, cavityFullTest μ T eig I u (cavityFullSpinInsertion Φ site) ∂θ) =
      ∫ T, cavityFullTest μ T eig I u (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ)) ∂θ := by
  rw [cavity_full_tree_site_identity hN μ θ eig I u hu Φ site]
  congr 1
  funext T
  congr 1
  funext σ
  exact (cavityOverlapWeightedTest_eq Φ
    (abs_le.mp (abs_cavityTotalSpinOverlap_le ((σ 0).1,(σ 1).1)))).symm

end InvariantIsing

end

end OAI
