import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundedDuality
import OAI.Analysis.LipschitzHilbert.Phase.DampedSimplexInterpolation
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

namespace OAI

/-! The scalar damped simplex theorem gives a dimension-independent Lp
estimate on each bounded exhaustion of the actual packet family. -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace LipschitzHilbert
variable {X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

theorem damped_simplex_barycenter_nonneg [DecidableEq ι] [Nonempty ι]
    (F : (ι → ℂ) → ℂ) (D : Set (ι → ℝ)) (hD : Convex ℝ D)
    (C mu : ℝ) (hC : 0 ≤ C)
    (hentire : ∀ a ∈ D, ∀ b ∈ D, ∀ eta,
      Differentiable ℂ (fun z => F (phaseTubeLine a b eta z)))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D,
      phaseTubeBound (fun z => gaussianPhaseDamping z*F z) M a)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvertex : ∀ i : ι,
      phaseTubeBound (fun z => gaussianPhaseDamping z*F z) C (Pi.single i mu)) :
    ‖F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))‖ ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply damped_simplex_barycenter F D hD (C+ε) mu (by linarith)
    hentire hbounded hvertices
  intro i eta
  exact (hvertex i eta).trans (le_add_of_nonneg_right hε.le)

theorem source_bounded_pairing_bound (μ : Measure X) [IsFiniteMeasure μ]
    (F b : X → EuclideanSpace ℂ κ) (hF : Measurable F) (hb : Measurable b)
    (A B p : ℝ) (hp : 1 < p) (hFA : ∀ x, ‖F x‖ ≤ A) (hbB : ∀ x, ‖b x‖ ≤ B) :
    ‖∫ x, ⟪b x,F x⟫_ℂ ∂μ‖ ≤
      (∫ x, ‖F x‖^p ∂μ)^(1/p)*(∫ x, ‖b x‖^(p/(p-1)) ∂μ)^(1/(p/(p-1))) := by
  have hFp : MemLp F (ENNReal.ofReal p) μ :=
    MemLp.of_bound hF.aestronglyMeasurable A (Filter.Eventually.of_forall hFA)
  have hbp : MemLp b (ENNReal.ofReal (p/(p-1))) μ :=
    MemLp.of_bound hb.aestronglyMeasurable B (Filter.Eventually.of_forall hbB)
  have hprod : Integrable (fun x => ‖F x‖*‖b x‖) μ := by
    apply (integrable_const (|A| * |B|)).mono' (hF.norm.mul hb.norm).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    change ‖‖F x‖*‖b x‖‖ ≤ |A| * |B|
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul ((hFA x).trans (le_abs_self A)) ((hbB x).trans (le_abs_self B))
      (norm_nonneg _) (abs_nonneg _)
  calc
    _ ≤ ∫ x, ‖⟪b x,F x⟫_ℂ‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖F x‖*‖b x‖ ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hprod
      exact Filter.Eventually.of_forall fun x => by
        simpa only [mul_comm] using norm_inner_le_norm (b x) (F x)
    _ ≤ _ := integral_mul_norm_le_Lp_mul_Lq (Real.HolderConjugate.conjExponent hp) hFp hbp

theorem source_simplex_lp_of_bounded_integrals [DecidableEq ι] [Nonempty ι]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : (ι → ℂ) → X → EuclideanSpace ℂ κ) (D : Set (ι → ℝ))
    (hD : Convex ℝ D) (p C mu : ℝ) (hp : 1 < p) (hC : 0 ≤ C)
    (hF : ∀ z, Measurable (F z)) (hFbound : ∀ z, ∃ A : ℝ, ∀ x, ‖F z x‖ ≤ A)
    (hentire : ∀ b : X → EuclideanSpace ℂ κ, Measurable b →
      (∃ B : ℝ, ∀ x, ‖b x‖ ≤ B) → ∀ a ∈ D, ∀ a' ∈ D, ∀ eta,
      Differentiable ℂ (fun z => ∫ x, ⟪b x,F (phaseTubeLine a a' eta z) x⟫_ℂ ∂μ))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D, ∀ eta x,
      ‖gaussianPhaseDamping (phaseTubePoint a eta) • F (phaseTubePoint a eta) x‖ ≤ M)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvertex : ∀ i : ι, ∀ eta,
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤ C) :
    (∫ x, ‖F (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0)) x‖^p ∂μ)^(1/p) ≤ C := by
  obtain ⟨A,hA⟩ := hFbound (phaseTubePoint (fun _ => mu/(Fintype.card ι:ℝ)) (fun _ => 0))
  apply source_bounded_lp_of_dual_tests μ _ (hF _) A C p hC hp hA
  intro b hb hbB
  obtain ⟨B,hB⟩ := hbB
  let t := (∫ x, ‖b x‖^(p/(p-1)) ∂μ)^(1/(p/(p-1)))
  have ht : 0 ≤ t := Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  let phi := fun z => ∫ x, ⟪b x,F z x⟫_ℂ ∂μ
  have hscale (z : ι → ℂ) : gaussianPhaseDamping z*phi z =
      ∫ x, ⟪b x,gaussianPhaseDamping z • F z x⟫_ℂ ∂μ := by
    simp_rw [inner_smul_right]
    exact (integral_const_mul _ _).symm
  refine damped_simplex_barycenter_nonneg phi D hD (C*t) mu (mul_nonneg hC ht)
    (hentire b hb ⟨B,hB⟩) ?_ hvertices ?_
  · obtain ⟨M,hM⟩ := hbounded
    refine ⟨(|B| * M)*μ.real univ,?_⟩
    intro a ha eta
    dsimp only
    rw [hscale]
    apply norm_integral_le_of_norm_le_const
    exact Filter.Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
      (mul_le_mul ((hB x).trans (le_abs_self _)) (hM a ha eta x)
        (norm_nonneg _) (abs_nonneg _))
  · intro i eta
    dsimp only
    rw [hscale]
    let z := phaseTubePoint (Pi.single i mu) eta
    obtain ⟨V,hV⟩ := hFbound z
    have hG : Measurable (fun x => gaussianPhaseDamping z • F z x) := by
      exact (measurable_const : Measurable (fun _ : X => gaussianPhaseDamping z)).smul (hF z)
    have hGV : ∀ x, ‖gaussianPhaseDamping z • F z x‖ ≤ ‖gaussianPhaseDamping z‖*V := by
      intro x
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hV x) (norm_nonneg _)
    exact (source_bounded_pairing_bound μ _ b hG hb _ B p hp hGV hB).trans
      (mul_le_mul_of_nonneg_right (hvertex i eta) ht)

end LipschitzHilbert

end

end OAI
