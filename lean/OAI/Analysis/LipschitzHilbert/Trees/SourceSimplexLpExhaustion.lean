import OAI.Analysis.LipschitzHilbert.Trees.SourceSimplexLpOn

namespace OAI

/-! Uniform vertex moments imply the full diagonal Lp estimate once
bounded analytic exhaustions have been constructed. -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace LipschitzHilbert
variable {X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

theorem source_simplex_lp_of_exhaustions [DecidableEq ι] [Nonempty ι]
    (μ : Measure X) [IsFiniteMeasure μ] (A : ℕ → Set X)
    (hA : ∀ n, MeasurableSet (A n)) (hmono : Monotone A) (hcover : (⋃ n, A n) = univ)
    (F : (ι → ℂ) → X → EuclideanSpace ℂ κ) (D : Set (ι → ℝ))
    (hD : Convex ℝ D) (p C mu : ℝ) (hp : 1 < p) (hC : 0 ≤ C)
    (hF : ∀ z, Measurable (F z))
    (hFbound : ∀ n z, ∃ V : ℝ, ∀ x ∈ A n, ‖F z x‖ ≤ V)
    (hentire : ∀ n, ∀ b : X → EuclideanSpace ℂ κ, Measurable b →
      (∃ B : ℝ, ∀ x, ‖b x‖ ≤ B) → ∀ a ∈ D, ∀ a' ∈ D, ∀ eta,
      Differentiable ℂ (fun z => ∫ x in A n, ⟪b x,F (phaseTubeLine a a' eta z) x⟫_ℂ ∂μ))
    (hbounded : ∀ n, ∃ M : ℝ, ∀ a ∈ D, ∀ eta x, x ∈ A n →
      ‖gaussianPhaseDamping (phaseTubePoint a eta) • F (phaseTubePoint a eta) x‖ ≤ M)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvint : ∀ i : ι, ∀ eta,
      Integrable (fun x => ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        F (phaseTubePoint (Pi.single i mu) eta) x‖^p) μ)
    (hvertex : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C) :
    let central := F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))
    Integrable (fun x => ‖central x‖^p) μ ∧ (∫ x, ‖central x‖^p ∂μ)^(1/p) ≤ C := by
  intro central
  have hp0 : 0 < p := by linarith
  apply source_lp_of_exhaustion μ central (hF _) p C hp0 hC A hmono hcover
  · intro n
    obtain ⟨V,hV⟩ := hFbound n (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))
    apply (integrable_const (|V|^p)).mono' ((hF _).norm.pow_const p).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (hA n)] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) ((hV x hx).trans (le_abs_self _)) hp0.le
  · intro n
    apply source_simplex_lp_on μ (A n) (hA n) F D hD p C mu hp hC hF
      (hFbound n) (hentire n) (hbounded n) hvertices
    intro i eta
    apply le_trans (Real.rpow_le_rpow
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
      (integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _) (hvint i eta))
      (one_div_pos.mpr hp0).le)
    exact hvertex i eta

end LipschitzHilbert

end

end OAI
