import OAI.Analysis.IrrationalRotation.Analysis.VonNeumannStrongClosure
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

noncomputable section
open Set
namespace Invariant233.Bicommutant

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def orbitSubmodule (A : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) : Submodule ℂ H where
  carrier := {y | ∃ a : H →L[ℂ] H, a ∈ A ∧ a x = y}
  zero_mem' := ⟨0, A.zero_mem, by simp⟩
  add_mem' := by
    rintro y z ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, A.add_mem ha hb, by simp⟩
  smul_mem' := by
    rintro c y ⟨a, ha, rfl⟩
    exact ⟨c • a, A.smul_mem ha c, by simp⟩

@[simp] theorem mem_orbitSubmodule (A : StarSubalgebra ℂ (H →L[ℂ] H)) (x y : H) :
    y ∈ orbitSubmodule A x ↔ ∃ a : H →L[ℂ] H, a ∈ A ∧ a x = y := Iff.rfl

theorem orbit_invariant (A : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H)
    {a : H →L[ℂ] H} (ha : a ∈ A) :
    orbitSubmodule A x ∈ Module.End.invtSubmodule a := by
  rintro y ⟨b, hb, rfl⟩
  exact ⟨a * b, A.mul_mem ha hb, rfl⟩

theorem closedOrbit_invariant (A : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H)
    {a : H →L[ℂ] H} (ha : a ∈ A) :
    (orbitSubmodule A x).topologicalClosure ∈ Module.End.invtSubmodule a :=
  Submodule.topologicalClosure_mem_invtSubmodule (orbit_invariant A x ha)

theorem projection_mem_centralizer (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (hS : ∀ a : H →L[ℂ] H, a ∈ A → S ∈ Module.End.invtSubmodule a) :
    S.starProjection ∈ Set.centralizer (A : Set (H →L[ℂ] H)) := by
  intro a ha
  have hc : Commute S.starProjection a := by
    apply (ContinuousLinearMap.IsIdempotentElem.commute_iff
      (isStarProjection_starProjection (U := S)).isIdempotentElem).2
    constructor
    · simpa only [Submodule.range_starProjection] using hS a ha
    · rw [Submodule.ker_starProjection]
      exact ContinuousLinearMap.orthogonal_mem_invtSubmodule (hS (star a) (star_mem ha))
  exact hc.symm.eq

theorem apply_mem_orbit_closure (A : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (x : H) : T x ∈ closure {y | ∃ a : H →L[ℂ] H, a ∈ A ∧ a x = y} := by
  let S := (orbitSubmodule A x).topologicalClosure
  let : CompleteSpace S := (Submodule.isClosed_topologicalClosure (orbitSubmodule A x)).completeSpace_coe
  have hP : S.starProjection ∈ Set.centralizer (A : Set (H →L[ℂ] H)) :=
    projection_mem_centralizer A S (fun a ha => closedOrbit_invariant A x ha)
  have hx : x ∈ S := Submodule.le_topologicalClosure _ ⟨1, A.one_mem, by simp⟩
  have hPx : S.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hPT := congrArg (fun a : H →L[ℂ] H => a x) (hT S.starProjection hP)
  have hTx : S.starProjection (T x) = T x := by
    simpa only [mul_apply_eq_comp, hPx] using hPT
  exact Submodule.starProjection_eq_self_iff.mp hTx

theorem exists_single_vector_approximation (A : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (x : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : H →L[ℂ] H, a ∈ A ∧ ‖a x - T x‖ < ε := by
  obtain ⟨y, ⟨a, ha, rfl⟩, hy⟩ :=
    Metric.mem_closure_iff.mp (apply_mem_orbit_closure A hT x) ε hε
  exact ⟨a, ha, by simpa only [dist_eq_norm, norm_sub_rev] using hy⟩

end Invariant233.Bicommutant

end

end OAI
