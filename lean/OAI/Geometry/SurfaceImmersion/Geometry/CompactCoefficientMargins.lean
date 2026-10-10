import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs
import OAI.Geometry.Immersion.ClosedSurface.PhaseMean

namespace OAI

/-! Positive phase coefficients admit an actual compact neighborhood and
uniform inner and outer trial-ball margins. -/
noncomputable section
open Set
open scoped Topology
namespace ClosedSurfaceR4.PhaseMean
open SmallModes (Base)

theorem compact_coefficient_margins {K Ω : Set Base} (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) {reference : Base → Tensor}
    (href : ContinuousOn reference Ω) (Q : Tensor →L[ℝ] ℝ)
    (hpos : ∀ x ∈ K, 0 < Q (reference x)) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧ closure U ⊆ Ω ∧
      ∃ r ρ R : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < R ∧
        ∀ x ∈ closure U, ρ + ‖Q‖*r ≤ Q (reference x) ∧
          Q (reference x) ≤ R - ‖Q‖*r := by
  have hf : ContinuousOn (fun x => Q (reference x)) Ω := Q.continuous.comp_continuousOn href
  obtain ⟨a,ha,hab⟩ := hK.exists_forall_le' (hf.mono hKΩ) hpos
  let O := Ω ∩ (fun x => Q (reference x)) ⁻¹' Ioi (a/2)
  have hO : IsOpen O := hf.isOpen_inter_preimage hΩ isOpen_Ioi
  have hKO : K ⊆ O := by
    intro x hx
    exact ⟨hKΩ hx,lt_of_lt_of_le (by linarith) (hab x hx)⟩
  obtain ⟨U,hU,hKU,hUc,hUO⟩ := CollarVelocity.compact_open_thickening hK hO hKO
  have hUΩ : closure U ⊆ Ω := fun x hx => (hUO hx).1
  obtain ⟨C,hC⟩ := hUc.exists_bound_of_continuousOn (hf.mono hUΩ)
  let r := (a/8)/(‖Q‖+1)
  have hr : 0 < r := div_pos (by linarith) (by positivity)
  have heq : (‖Q‖+1)*r = a/8 := by
    dsimp [r]
    field_simp
  have hnr : ‖Q‖*r ≤ a/8 := by nlinarith [norm_nonneg Q]
  refine ⟨U,hU,hKU,hUc,hUΩ,r,a/8,|C|+‖Q‖*r+1,hr,by linarith,by positivity,?_⟩
  intro x hx
  have hl : a/2 < Q (reference x) := (hUO hx).2
  have hu : Q (reference x) ≤ |C| :=
    (le_abs_self _).trans ((hC x hx).trans (le_abs_self C))
  constructor <;> linarith

end ClosedSurfaceR4.PhaseMean

end

end OAI
