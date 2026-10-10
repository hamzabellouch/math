import OAI.Geometry.NodalSets.Coefficients.GaussianCoefficientVariance

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

lemma standard_gaussian_abs_tail {r : ℝ} (hr : 0 ≤ r) :
    gaussianReal 0 1 {x | r ≤ |x|} ≤ ENNReal.ofReal (2*Real.exp (-r^2/2)) := by
  have hu := measure_ge_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 1) r hr
    (integrable_exp_mul_gaussianReal r)
  have hl := measure_le_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 1) (-r)
    (neg_nonpos.mpr hr) (integrable_exp_mul_gaussianReal (-r))
  simp only [mgf_id_gaussianReal,zero_mul,NNReal.coe_one,one_mul,zero_add,
    ← Real.exp_add] at hu hl
  have heu : -r*r+r^2/2 = -r^2/2 := by ring
  have hel : -(-r)*(-r)+(-r)^2/2 = -r^2/2 := by ring
  rw [heu] at hu
  rw [hel] at hl
  have hu' := ENNReal.ofReal_le_ofReal hu
  have hl' := ENNReal.ofReal_le_ofReal hl
  rw [ofReal_measureReal] at hu' hl'
  have hsub : {x : ℝ | r ≤ |x|} ⊆ {x | r ≤ id x} ∪ {x | id x ≤ -r} := by
    intro x hx
    change r ≤ |x| at hx
    rcases le_abs.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (by dsimp; linarith)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have h := add_le_add hu' hl'
  rw [two_mul,ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  exact h

variable {ι : Type*} [Fintype ι]

def coefficientEvent (r : ℝ) : Set (ι × Fin 2 → ℝ) :=
  {a | ∀ i, ‖(a (i,0) : ℂ)+Complex.I*(a (i,1):ℂ)‖ ≤ r}

lemma gaussian_pairs_coordinate_tail {r : ℝ} (hr : 0 ≤ r) (p : ι × Fin 2) :
    (gaussianPairs (ι := ι)) {a | r ≤ |a p|} ≤ ENNReal.ofReal (2*Real.exp (-r^2/2)) := by
  classical
  have hm := (measurePreserving_eval (fun _ : ι × Fin 2 ↦ gaussianReal 0 1) p).map_eq
  have h := standard_gaussian_abs_tail hr
  rw [← hm,Measure.map_apply (by fun_prop) (measurableSet_le measurable_const (by fun_prop))] at h
  exact h

theorem coefficient_event_failure {r : ℝ} (hr : 0 ≤ r) :
    (gaussianPairs (ι := ι)) (coefficientEvent (ι := ι) r)ᶜ ≤
      ENNReal.ofReal (4*(Fintype.card ι:ℝ)*Real.exp (-r^2/8)) := by
  classical
  have hsub : (coefficientEvent (ι := ι) r)ᶜ ⊆
      ⋃ p : ι × Fin 2, {a | r/2 ≤ |a p|} := by
    intro a ha
    change ¬ ∀ i, ‖(a (i,0):ℂ)+Complex.I*(a (i,1):ℂ)‖ ≤ r at ha
    push Not at ha
    obtain ⟨i,hi⟩ := ha
    have hb : ‖(a (i,0):ℂ)+Complex.I*(a (i,1):ℂ)‖ ≤ |a (i,0)|+|a (i,1)| := by
      simpa using norm_add_le (a (i,0):ℂ) (Complex.I*(a (i,1):ℂ))
    have he : r/2 ≤ |a (i,0)| ∨ r/2 ≤ |a (i,1)| := by
      by_contra hh
      push Not at hh
      linarith
    rcases he with h | h
    · exact mem_iUnion.mpr ⟨(i,0),h⟩
    · exact mem_iUnion.mpr ⟨(i,1),h⟩
  have h := (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
    (Finset.sum_le_sum (fun p _ ↦ gaussian_pairs_coordinate_tail (div_nonneg hr (by norm_num)) p)))
  have he : -(r/2)^2/2 = -r^2/8 := by ring
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin] at h
  convert h using 1
  simp only [nsmul_eq_mul,Nat.cast_mul]
  norm_num
  ring

end
end Yau.Probability

end OAI
