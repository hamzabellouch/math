import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticInverseChart
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticRepresentationAtlas

namespace OAI

/-! # Matrix coordinates from an analytic represented local parameter -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped ContDiff

variable {G E A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedRing A] [NormedAlgebra ℝ A]

omit [IsTopologicalGroup G] in
theorem representedLocalChart_of_parameter
    (ρ : G →* Aˣ) (p : OpenPartialHomeomorph E G)
    (hp : (0 : E) ∈ p.source) (hp0 : p 0 = 1)
    (P : A →L[ℝ] E) (U V : E → A)
    (hU : ContDiff ℝ ω U) (hV : ContDiff ℝ ω V)
    (heU : ∀ x ∈ p.source, U x = (ρ (p x) : A))
    (heV : ∀ x ∈ p.source, V x = ((ρ (p x))⁻¹ : Aˣ))
    (hd : HasFDerivAt (fun x => P (U x - 1)) (ContinuousLinearMap.id ℝ E) 0) :
    Nonempty (RepresentedLocalChart (E := E) ρ) := by
  have hU0 : U 0 = 1 := by rw [heU 0 hp,hp0,map_one,Units.val_one]
  have hQ : ContDiff ℝ ω (fun x => P (U x - 1)) :=
    P.contDiff.comp (hU.sub contDiff_const)
  have hQ0 : P (U 0 - 1) = 0 := by rw [hU0,sub_self,map_zero]
  obtain ⟨q,hq0,hqzero,hq,hqi⟩ := exists_analytic_inverse_chart hQ.contDiffAt hQ0 hd
  have hpinv : p.symm (1 : G) = 0 := by rw [← hp0]; exact p.left_inv hp
  let e := p.symm.trans q
  have heone : (1 : G) ∈ e.source := by
    refine ⟨hp0 ▸ p.map_source hp, ?_⟩
    change p.symm 1 ∈ q.source
    rwa [hpinv]
  have hetarget : e.target ⊆ q.target := fun _ hx => hx.1
  refine ⟨{
    chart := e
    one_mem := heone
    at_one := ?_
    coordinate := P
    coordinate_eq := ?_
    realization := U ∘ q.symm
    realization_contDiff := hU.comp_contDiffOn (hqi.mono hetarget)
    realization_eq := ?_
    inverseRealization := V ∘ q.symm
    inverseRealization_contDiff := hV.comp_contDiffOn (hqi.mono hetarget)
    inverseRealization_eq := ?_ }⟩
  · change q (p.symm 1) = 0
    rw [hpinv,hqzero]
  · intro g hg
    change q (p.symm g) = P ((ρ g : A) - 1)
    rw [hq]
    change P (U (p.symm g) - 1) = _
    rw [heU _ (p.map_target hg.1),p.right_inv hg.1]
  · intro x hx
    exact heU (q.symm x) hx.2
  · intro x hx
    exact heV (q.symm x) hx.2

end PolycyclicRecognition

end

end OAI
