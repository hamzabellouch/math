import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicCalculus
import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyProfile

namespace OAI

/-! The two-turn estimates on a half-open period also hold at the closed
endpoint needed for compact profile estimates. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes

lemma closed_interval_turns {U K : Set Base} (hU : IsOpen U) (hKU : K ⊆ U)
    {α : Base × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (U ×ˢ univ))
    (hper : ∀ x ∈ U, Function.Periodic (fun t => α (x,t)) 1)
    {τ : Base → ℝ} {Λ : ℝ}
    (hturn : ∀ x ∈ K, ∀ t ∈ Ico (0 : ℝ) 1,
      deriv (fun s => α (x,s)) t = 0 ↔ t = 0 ∨ t = τ x)
    (hlarge : ∀ x ∈ K,
      Λ < fderiv ℝ (fun y => α (y,0)) x dy ∧
      Λ < fderiv ℝ (fun y => α (y,τ x)) x dy) :
    ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
      fderiv ℝ α (x,t) (0,1) = 0 → Λ < fderiv ℝ α (x,t) (dy,0) := by
  intro x hx t ht hz
  have hxU := hKU hx
  have hs (t : ℝ) : fderiv ℝ (fun y => α (y,t)) x dy = fderiv ℝ α (x,t) (dy,0) :=
    fderiv_slice_first
      ((hα.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hxU,mem_univ t⟩)).differentiableAt (by simp)) dy
  rw [← hs]
  rcases lt_or_eq_of_le ht.2 with ht1 | rfl
  · have hd : deriv (fun s => α (x,s)) t = 0 := by
      rw [(LocalPeriodicCalculus.angle_hasDerivAt hU hα hxU t).deriv]
      exact hz
    rcases (hturn x hx t ⟨ht.1,ht1⟩).mp hd with rfl | rfl
    · exact (hlarge x hx).1
    · exact (hlarge x hx).2
  · have he : (fun y => α (y,1)) =ᶠ[𝓝 x] (fun y => α (y,0)) := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      simpa only [zero_add] using hper y hy 0
    rw [he.fderiv_eq]
    exact (hlarge x hx).1

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
