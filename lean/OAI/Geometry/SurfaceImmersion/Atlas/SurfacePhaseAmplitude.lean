import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseCharts
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! A genuinely smooth amplitude in phase coordinates, extended by zero
with precisely the original support and no change to its surface values. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_phase_amplitude (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hDc : IsCompact (closure D))
    (hDs : closure D ⊆ (surfacePhaseChart q e).source)
    {f : M → ℝ} (hf : ContMDiff planeModel 𝓘(ℝ) ∞ f)
    (hf0 : ∀ p, 0 ≤ f p) (hfpos : ∀ p, 0 < f p ↔ p ∈ D) :
    ∃ a : SmallModes.Base → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 ≤ a x) ∧
      (∀ p ∈ (surfacePhaseChart q e).source, a (surfacePhaseChart q e p) = f p) ∧
      (∀ x, 0 < a x ↔ x ∈ (surfacePhaseChart q e) '' D) ∧
      ∀ x ∉ (surfacePhaseChart q e) '' closure D, a x = 0 := by
  let E := surfacePhaseChart q e
  let K := E '' closure D
  have hK : IsCompact K := hDc.image_of_continuousOn (E.continuousOn.mono hDs)
  have hKt : K ⊆ E.target := by
    rintro _ ⟨p,hp,rfl⟩
    exact E.map_source (hDs hp)
  obtain ⟨β,hβ,hβc,hβrange,hβs,hβone⟩ :=
    CollarVelocity.compact_cutoff hK E.open_target hKt
  have hraw : ContDiffOn ℝ ∞ (f ∘ E.symm) E.target := by
    exact (hf.comp_contMDiffOn (surfacePhaseChart_symm_smooth q e hi)).contDiffOn
  let a := fun x => β x * f (E.symm x)
  have ha : ContDiff ℝ ∞ a :=
    CollarVelocity.supported_local_mul E.open_target hβ hraw hβs
  have hzero {p : M} (hp : p ∉ D) : f p = 0 :=
    le_antisymm (le_of_not_gt (fun hh => hp ((hfpos p).mp hh))) (hf0 p)
  have heq (p : M) (hp : p ∈ E.source) : a (E p) = f p := by
    change β (E p)*f (E.symm (E p)) = f p
    rw [E.left_inv hp]
    by_cases hpD : p ∈ closure D
    · rw [hβone _ (mem_image_of_mem E hpD),one_mul]
    · rw [hzero (fun hh => hpD (subset_closure hh)),mul_zero]
  refine ⟨a,ha,fun x => mul_nonneg (hβrange x).1 (hf0 _),heq,?_,?_⟩
  · intro x
    constructor
    · intro hx
      have hbx : β x ≠ 0 := by intro hz; change 0 < β x*f (E.symm x) at hx; rw [hz,zero_mul] at hx; exact lt_irrefl _ hx
      have hxt : x ∈ E.target := hβs (subset_tsupport β hbx)
      have hfx : 0 < f (E.symm x) := by
        rw [← E.right_inv hxt,heq _ (E.map_target hxt)] at hx
        exact hx
      exact ⟨E.symm x,(hfpos _).mp hfx,E.right_inv hxt⟩
    · rintro ⟨p,hp,rfl⟩
      rw [heq _ (hDs (subset_closure hp))]
      exact (hfpos p).mpr hp
  · intro x hx
    by_cases hb0 : β x = 0
    · exact by change β x*f (E.symm x) = 0; rw [hb0,zero_mul]
    have hxt : x ∈ E.target := hβs (subset_tsupport β hb0)
    have hpD : E.symm x ∉ D := by
      intro hp
      exact hx ⟨E.symm x,subset_closure hp,E.right_inv hxt⟩
    exact by change β x*f (E.symm x) = 0; rw [hzero hpD,mul_zero]

end ClosedSurfaceR4

end

end OAI
