import OAI.Geometry.SurfaceImmersion.Geometry.CompactCoefficientMargins
import OAI.Geometry.Immersion.ClosedSurface.ImmersionJets
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseSupportCoordinates

namespace OAI

/-! Compact good geometry supplies the open domains and strict coefficient
margins needed by the actual local mean construction. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean

theorem compact_good_phase_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (K : Compacts Base) (hImm : ∀ x ∈ (K : Set Base), Function.Injective (fderiv ℝ F x))
    (ξ : Base) (hgood : ∀ x ∈ (K : Set Base), Good (realSecondTensor F x) ξ) :
    ∃ Ω : Set Base, IsOpen Ω ∧ (K : Set Base) ⊆ Ω ∧
      ∀ x ∈ Ω, Function.Injective (fderiv ℝ F x) ∧ Good (realSecondTensor F x) ξ := by
  let Ω : Set Base := {x | NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0 ∧
    Good (realSecondTensor F x) ξ}
  have hΩ : IsOpen Ω := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hd := (continuous_gramDet_field hF).continuousAt.eventually_ne hx.1
    have hg := good_eventually (contDiffAt_realSecondTensor hF x hx.1).continuousAt
      continuousAt_const hx.2
    exact hd.and hg
  refine ⟨Ω,hΩ,?_,?_⟩
  · intro x hx
    exact ⟨gramDet_ne_zero_of_injective _ (hImm x hx),hgood x hx⟩
  · intro x hx
    exact ⟨injective_of_gramDet_ne_zero _ hx.1,hx.2⟩

/-- The three phases share positive trial and coefficient radii. All domains
and radii are chosen from the fixed compact reference geometry. -/
theorem compact_phase_mean_domains {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (K : Compacts Base) (hImm : ∀ x ∈ (K : Set Base), Function.Injective (fderiv ℝ F x))
    (ξ : Fin 3 → Base)
    (hgood : ∀ j x, x ∈ (K : Set Base) → Good (realSecondTensor F x) (ξ j))
    (Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ) (H : Base → PhaseMean.Tensor) (hH : Continuous H)
    (hpos : ∀ j x, x ∈ (K : Set Base) → 0 < Q j (H x)) :
    ∃ r ρ R : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < R ∧
      ∃ U K₁ Ω : Fin 3 → Set Base,
        (∀ j, IsOpen (U j)) ∧ (∀ j, IsCompact (K₁ j)) ∧ (∀ j, IsOpen (Ω j)) ∧
        (∀ j, (K : Set Base) ⊆ U j) ∧ (∀ j, U j ⊆ K₁ j) ∧ (∀ j, K₁ j ⊆ Ω j) ∧
        (∀ j x, x ∈ Ω j → Function.Injective (fderiv ℝ F x) ∧
          Good (realSecondTensor F x) (ξ j)) ∧
        (∀ j x, x ∈ K₁ j → ρ + ‖Q j‖*r ≤ Q j (H x) ∧
          Q j (H x) ≤ R - ‖Q j‖*r) := by
  classical
  choose Ω hΩ hKΩ hgeom using fun j =>
    compact_good_phase_neighborhood hF K hImm (ξ j) (hgood j)
  choose U hU hKU hUc hUΩ a b c ha hb hc hmargin using fun j =>
    compact_coefficient_margins K.isCompact (hΩ j) (hKΩ j) hH.continuousOn (Q j) (hpos j)
  let r := min (a 0) (min (a 1) (a 2))
  let ρ := min (b 0) (min (b 1) (b 2))
  let R := ∑ j : Fin 3, c j
  have hr : 0 < r := lt_min (ha 0) (lt_min (ha 1) (ha 2))
  have hρ : 0 < ρ := lt_min (hb 0) (lt_min (hb 1) (hb 2))
  have hra (j : Fin 3) : r ≤ a j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hρb (j : Fin 3) : ρ ≤ b j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hcR (j : Fin 3) : c j ≤ R :=
    Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ j)
  have hR : 0 < R := (hc 0).trans_le (hcR 0)
  refine ⟨r,ρ,R,hr,hρ,hR,U,(fun j => closure (U j)),Ω,
    hU,hUc,hΩ,hKU,(fun _ => subset_closure),hUΩ,hgeom,?_⟩
  intro j x hx
  have hm := hmargin j x hx
  have hn : ‖Q j‖*r ≤ ‖Q j‖*a j :=
    mul_le_mul_of_nonneg_left (hra j) (norm_nonneg _)
  have hl := hρb j
  have hu := hcR j
  constructor <;> linarith

/-- The original-coordinate coefficient domain can always be chosen open
and bounded while containing the compact phase support. -/
theorem compact_phase_original_domain (K : Compacts Base) :
    ∃ (U₀ : Set JetPolynomial.Base) (K₀ : Compacts JetPolynomial.Base),
      IsOpen U₀ ∧ U₀ ⊆ K₀ ∧
      (JetPolynomial.Perturbation.jetSupport K : Set JetPolynomial.Base) ⊆ U₀ := by
  obtain ⟨U,hU,hKU,hUc,_⟩ := CollarVelocity.compact_open_thickening
    (JetPolynomial.Perturbation.jetSupport K).isCompact isOpen_univ (subset_univ _)
  exact ⟨U,⟨closure U,hUc⟩,hU,subset_closure,hKU⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
