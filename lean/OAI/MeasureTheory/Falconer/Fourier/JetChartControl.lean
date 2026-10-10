import OAI.MeasureTheory.Falconer.Fourier.UniformJetBudget
import OAI.MeasureTheory.Falconer.Fourier.DescriptorJetMeasurable
import OAI.MeasureTheory.Falconer.Geometry.AmbientChartBudget
import OAI.MeasureTheory.Falconer.Fourier.ChartSymbolControl

namespace OAI

/-! # Rotated chart control for the actual finite products of mask jets

The total derivative order pays the amplitude cost. The number of mask
occurrences enters the derivative scale, and no occurrence is discarded.
All constants are selected before the scale, descriptors, and index type.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

 theorem descriptorJetProduct_chartControl (n K L : ℕ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧
      ∀ {ι : Type*} (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2)))
        (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
        (b : ι → PlanarFalconer.PolicyDescriptor)
        (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+2)))
        (k : ι → ℕ) (v : (j : ι) → Fin (k j) → Space (n+2)),
      (∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
        descriptorMaskRadius N σ (b j)/2 ≤ dist w z) →
      (∑ j ∈ F, k j) ≤ K → (∀ j ∈ F, ∀ t, ‖v j t‖ ≤ 1) →
      ∀ D E : ℝ, 1 ≤ D → 1 ≤ E →
      (∀ j ∈ F, (descriptorMaskRadius N σ (b j))⁻¹ ≤ D) →
      (F.card:ℝ)*A*D ≤ E →
      ChartSymbolControl L
        (descriptorJetProduct Q ρ m N σ J i F b S k (fun j _ => v j)) (C*A^K) E := by
  classical
  obtain ⟨A,hA,hAb⟩ := normalizedAmbientJetProduct_uniform_budget (n+2) K L
  obtain ⟨H,hH,hHb⟩ := ambient_symbol_rotated_chart_budget n L
  refine ⟨A,H+1,hA,by linarith,?_⟩
  intro ι Q ρ m N σ J i F b S k v hsep horder hv D E hD hE hscale hDE
  let B : Space (n+2) → Space (n+2) → ℝ := fun x z =>
    ∏ j ∈ F, normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x z
  let Z : Space (n+2) → Space (n+2) → ℂ := fun x z => (B x z : ℂ)
  have hB (x : Space (n+2)) : ContDiff ℝ ∞ (B x) :=
    contDiff_prod (fun j _ => normalizedAmbientDescriptorJet_contDiff
      Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x)
  have hZ (x : Space (n+2)) : ContDiff ℝ ∞ (Z x) :=
    Complex.ofRealCLM.contDiff.comp (hB x)
  have he : descriptorJetProduct Q ρ m N σ J i F b S k (fun j _ => v j) =
      fun x (w : Sphere (n+2)) => Z x w := by
    funext x w
    simp only [descriptorJetProduct,Z,B,Complex.ofReal_prod,normalizedAmbientDescriptorJet_sphere]
  have hm := descriptorJetProduct_measurable Q ρ m N σ J i F b S k
    (fun j _ => v j) (fun _ _ => measurable_const)
  rw [he] at hm ⊢
  have hAK : 0 ≤ A^K := pow_nonneg (zero_le_one.trans hA) _
  have hjet (x : Space (n+2)) (t : ℕ) (ht : t ≤ L) (w : Sphere (n+2)) :
      ‖iteratedFDeriv ℝ t (Z x) w‖ ≤ A^K*E^t := by
    have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      ((hB x).contDiffAt (x := (w : Space (n+2)))) (by simp : (t : ℕ∞ω) ≤ ∞)
    change ‖iteratedFDeriv ℝ t (Complex.ofRealLI ∘ B x) w‖ ≤ _
    rw [hn]
    exact (hAb Q ρ m N σ J i F b S k v hsep horder hv D hD hscale x w t ht).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hDE t) hAK)
  refine ⟨hm,?_,?_,?_⟩
  · intro x w
    have h := hjet x 0 (Nat.zero_le _) w
    simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at h
    exact h.trans (le_mul_of_one_le_left hAK (by linarith))
  · intro x e y
    exact (hZ x).comp (rotatedChartCurve_contDiff e y)
  · intro e t ht x y hy u hu
    have h := hHb (Z x) (hZ x) (A^K) E hAK hE (hjet x) e y hy u hu t ht
    exact h.trans (by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show H ≤ H+1 by linarith) hAK)
        (pow_nonneg (zero_le_one.trans hE) t)
      simpa only [mul_assoc] using this)

end Falconer

end OAI
