import OAI.Analysis.FiniteFactor.Diffuse.OperatorMeanErgodic
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual orthogonal projection onto the closed range of an operator. -/
def rangeSupport (T : H →L[ℂ] H) : H →L[ℂ] H :=
  T.range.topologicalClosure.starProjection

lemma rangeSupport_projection (T : H →L[ℂ] H) : IsStarProjection (rangeSupport T) :=
  isStarProjection_starProjection

lemma rangeSupport_range (T : H →L[ℂ] H) :
    (rangeSupport T).range=T.range.topologicalClosure :=
  Submodule.range_starProjection _

lemma rangeSupport_mul_self (T : H →L[ℂ] H) : rangeSupport T*T=T := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact Submodule.le_topologicalClosure _ ⟨x,rfl⟩

lemma rangeSupport_ne_zero {T : H →L[ℂ] H} (hT:T≠0) : rangeSupport T≠0 := by
  intro h
  have he:=rangeSupport_mul_self T
  rw [h,zero_mul] at he
  exact hT he.symm

/-- Closed range support belongs to the same concrete von Neumann algebra. -/
theorem rangeSupport_mem (M : VonNeumannAlgebra H) {T:H→L[ℂ]H} (hT:T∈M) :
    rangeSupport T∈M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff (rangeSupport_projection T) M).mpr
  intro y hy
  rw [rangeSupport_range]
  apply Submodule.topologicalClosure_mem_invtSubmodule
  intro x hx
  obtain ⟨z,rfl⟩:=hx
  refine ⟨y z,?_⟩
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp hy T hT
  exact congrArg (fun A:H→L[ℂ]H=>A z) hc

lemma projection_mul_rangeSupport {p T:H→L[ℂ]H} (hp:IsStarProjection p) (h:p*T=T) :
    p*rangeSupport T=rangeSupport T := by
  have hs : Set.EqOn p id (T.range:Set H) := by
    rintro _ ⟨x,rfl⟩
    have hx : T x ∈ p.range := ⟨T x, congrArg (fun A:H→L[ℂ]H=>A x) h⟩
    obtain ⟨y,hy⟩ := hx
    change p (T x) = T x
    rw [← hy]
    exact congrArg (fun A:H→L[ℂ]H=>A y) hp.isIdempotentElem.eq
  have hc : Set.EqOn p id (closure (T.range:Set H)) :=
    hs.closure p.continuous continuous_id
  ext x
  exact hc (T.range.topologicalClosure.starProjection_apply_mem x)

lemma rangeSupport_mul_projection {p T:H→L[ℂ]H} (hp:IsStarProjection p) (h:p*T=T) :
    rangeSupport T*p=rangeSupport T := by
  have he:=congrArg star (projection_mul_rangeSupport hp h)
  simpa only [star_mul,hp.isSelfAdjoint.star_eq,(rangeSupport_projection T).isSelfAdjoint.star_eq] using he

end Nonhyperlinear.Diffuseness

end

end OAI
