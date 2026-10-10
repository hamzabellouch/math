import OAI.Analysis.LipschitzHilbert.Trees.SourceLpExhaustion

namespace OAI

/-! Restricted-set form of the bounded simplex estimate. The zero
extension supplies bounded tests on the ambient finite measure space. -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace LipschitzHilbert
variable {X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

theorem source_integral_inner_indicator (μ : Measure X) (A : Set X) (hA : MeasurableSet A)
    (F b : X → EuclideanSpace ℂ κ) :
    (∫ x, ⟪b x,A.indicator F x⟫_ℂ ∂μ) = ∫ x in A, ⟪b x,F x⟫_ℂ ∂μ := by
  classical
  rw [← integral_indicator hA]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ A <;> simp [hx]

theorem source_integral_norm_indicator_power (μ : Measure X) (A : Set X) (hA : MeasurableSet A)
    (F : X → EuclideanSpace ℂ κ) (c : ℂ) (p : ℝ) (hp : p ≠ 0) :
    (∫ x, ‖c • A.indicator F x‖^p ∂μ) = ∫ x in A, ‖c • F x‖^p ∂μ := by
  classical
  rw [← integral_indicator hA]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ A <;> simp [hx,Real.zero_rpow hp]

theorem source_simplex_lp_on [DecidableEq ι] [Nonempty ι]
    (μ : Measure X) [IsFiniteMeasure μ] (A : Set X) (hA : MeasurableSet A)
    (F : (ι → ℂ) → X → EuclideanSpace ℂ κ) (D : Set (ι → ℝ))
    (hD : Convex ℝ D) (p C mu : ℝ) (hp : 1 < p) (hC : 0 ≤ C)
    (hF : ∀ z, Measurable (F z)) (hFbound : ∀ z, ∃ V : ℝ, ∀ x ∈ A, ‖F z x‖ ≤ V)
    (hentire : ∀ b : X → EuclideanSpace ℂ κ, Measurable b →
      (∃ B : ℝ, ∀ x, ‖b x‖ ≤ B) → ∀ a ∈ D, ∀ a' ∈ D, ∀ eta,
      Differentiable ℂ (fun z => ∫ x in A, ⟪b x,F (phaseTubeLine a a' eta z) x⟫_ℂ ∂μ))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D, ∀ eta x, x ∈ A →
      ‖gaussianPhaseDamping (phaseTubePoint a eta) • F (phaseTubePoint a eta) x‖ ≤ M)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvertex : ∀ i : ι, ∀ eta,
      (∫ x in A, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C) :
    (∫ x in A, ‖F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0)) x‖^p ∂μ)^(1/p) ≤ C := by
  classical
  let G := fun z => A.indicator (F z)
  have hG : ∀ z, Measurable (G z) := fun z => (hF z).indicator hA
  have hGb : ∀ z, ∃ V : ℝ, ∀ x, ‖G z x‖ ≤ V := by
    intro z
    obtain ⟨V,hV⟩ := hFbound z
    refine ⟨|V|,?_⟩
    intro x
    by_cases hx : x ∈ A
    · have hz : ‖G z x‖ ≤ V := by simpa only [G,indicator_of_mem hx] using hV x hx
      exact hz.trans (le_abs_self _)
    · simpa only [G,indicator_of_notMem hx,norm_zero] using abs_nonneg V
  have he : ∀ b : X → EuclideanSpace ℂ κ, Measurable b →
      (∃ B : ℝ, ∀ x, ‖b x‖ ≤ B) → ∀ a ∈ D, ∀ a' ∈ D, ∀ eta,
      Differentiable ℂ (fun z => ∫ x, ⟪b x,G (phaseTubeLine a a' eta z) x⟫_ℂ ∂μ) := by
    intro b hb hbB a ha a' ha' eta
    simp_rw [G,source_integral_inner_indicator μ A hA]
    exact hentire b hb hbB a ha a' ha' eta
  have hbd : ∃ M : ℝ, ∀ a ∈ D, ∀ eta x,
      ‖gaussianPhaseDamping (phaseTubePoint a eta) • G (phaseTubePoint a eta) x‖ ≤ M := by
    obtain ⟨M,hM⟩ := hbounded
    refine ⟨|M|,?_⟩
    intro a ha eta x
    by_cases hx : x ∈ A
    · have hz : ‖gaussianPhaseDamping (phaseTubePoint a eta) • G (phaseTubePoint a eta) x‖ ≤ M := by
        simpa only [G,indicator_of_mem hx] using hM a ha eta x hx
      exact hz.trans (le_abs_self _)
    · simpa only [G,indicator_of_notMem hx,smul_zero,norm_zero] using abs_nonneg M
  have hv : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        G (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C := by
    intro i eta
    rw [source_integral_norm_indicator_power μ A hA _ _ _ (by linarith)]
    exact hvertex i eta
  have h := source_simplex_lp_of_bounded_integrals μ G D hD p C mu hp hC hG hGb he hbd hvertices hv
  have hi := source_integral_norm_indicator_power μ A hA
    (F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))) (1:ℂ) p (by linarith)
  simp only [one_smul] at hi
  change (∫ x, ‖A.indicator (F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))) x‖^p ∂μ)^(1/p) ≤ C at h
  rwa [hi] at h

end LipschitzHilbert

end

end OAI
