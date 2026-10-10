import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import OAI.Probability.CriticalPercolation.Criticality.CylinderApproximation

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical symmDiff ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

lemma invariant_zero_one (p : unitInterval) (ρ : I → E ≃ E)
    (hdisp : ∀ S : Finset E, ∃ i, Disjoint (S : Set E) ((ρ i).symm '' (S : Set E)))
    (A : Set (Set E)) (hA : MeasurableSet A)
    (hinv : ∀ i, (fun ω : Set E => ρ i '' ω) ⁻¹' A = A) :
    law (fun _ : E => p) A = 0 ∨ law (fun _ : E => p) A = 1 := by
  let μ := law (fun _ : E => p)
  have hsq : μ.real A ≤ (μ.real A)^2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hδ : 0 < ε/4 := by positivity
    obtain ⟨S,B,hB,happrox⟩ := exists_finiteCoordinate_approx (fun _ : E => p) hA
      (ENNReal.ofReal_pos.mpr hδ)
    have hBm : MeasurableSet B := blockSigma_le _ _ hB
    obtain ⟨i,hi⟩ := hdisp S
    let f : Set E → Set E := fun ω => ρ i '' ω
    let C := f ⁻¹' B
    have hf : Measurable f := measurable_image_equiv (ρ i)
    have hC : MeasurableSet[blockSigma ((ρ i).symm '' (S : Set E))] C :=
      (measurable_image_equiv_blocks (ρ i) (S : Set E)) hB
    have hCm : MeasurableSet C := hBm.preimage hf
    have hind : IndepSet B C μ :=
      (independent_disjoint_blocks (fun _ => p) (S : Set E) _ hi).indepSet_of_measurableSet hB hC
    have hpres (D : Set (Set E)) (hD : MeasurableSet D) : μ.real (f ⁻¹' D) = μ.real D := by
      change (μ (f ⁻¹' D)).toReal = (μ D).toReal
      rw [← Measure.map_apply hf hD]
      change ((law (fun _ : E => p)).map (fun ω => ρ i '' ω) D).toReal = _
      rw [law_map_equiv]
    have hCeq : μ.real C = μ.real B := hpres B hBm
    have hAB : μ.real (B ∆ A) ≤ ε/4 := by
      apply le_of_lt
      have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr happrox
      change (μ (B ∆ A)).toReal < ε/4
      rwa [ENNReal.toReal_ofReal hδ.le] at hh
    have hAC : μ.real (C ∆ A) ≤ ε/4 := by
      have he : C ∆ A = f ⁻¹' (B ∆ A) := by
        rw [Set.preimage_symmDiff,hinv]
      rw [he,hpres _ (hBm.symmDiff hA)]
      exact hAB
    have hcover : A ⊆ (B ∩ C) ∪ ((B ∆ A) ∪ (C ∆ A)) := by
      intro ω hω
      simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_symmDiff]
      tauto
    have hinter : μ.real (B ∩ C) = (μ.real B)^2 := by
      rw [measureReal_def,hind.measure_inter_eq_mul,ENNReal.toReal_mul]
      change μ.real B * μ.real C = _
      rw [hCeq,pow_two]
    have hbound : μ.real A ≤ (μ.real B)^2 + ε/2 := by
      have hh := (measureReal_mono hcover (μ := μ)).trans
        (measureReal_union_le (B ∩ C) ((B ∆ A) ∪ (C ∆ A)))
      have hu := measureReal_union_le (B ∆ A) (C ∆ A) (μ := μ)
      rw [hinter] at hh
      linarith
    have hdif : μ.real B - μ.real A ≤ ε/4 :=
      (le_abs_self _).trans ((abs_measureReal_sub_le_measureReal_symmDiff
        hBm.nullMeasurableSet hA.nullMeasurableSet).trans hAB)
    have hfac : (μ.real B - μ.real A)*(μ.real A + μ.real B) ≤ (ε/4)*2 := by
      apply (mul_le_mul_of_nonneg_right hdif (add_nonneg measureReal_nonneg measureReal_nonneg)).trans
      exact mul_le_mul_of_nonneg_left (by
        have ha := measureReal_le_one (μ := μ) (s := A)
        have hb := measureReal_le_one (μ := μ) (s := B)
        linarith) hδ.le
    nlinarith only [hbound,hfac]
  have ha0 : 0 ≤ μ.real A := measureReal_nonneg
  have ha1 : μ.real A ≤ 1 := measureReal_le_one
  have heq : μ.real A = 0 ∨ μ.real A = 1 := by
    have h : μ.real A * (μ.real A - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases heq with h | h
  · left
    exact (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (measure_ne_top μ A)
  · right
    exact (ENNReal.toReal_eq_one_iff _).mp h

end CriticalPercolation.BernoulliProduct
end
end

end OAI
