import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteKernelAscendingBase
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AscendingFinitenessEndgame

namespace OAI

/-! # Finite kernels above the ascending structural case

The full height, letter and stable base are lifted along the homomorphism.
Thus a finite-by-ascending virtually nilpotent group satisfies the same
finite-index solvable finite-dimension conclusion.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G Q : Type} [Group G] [Group Q]

def AscendingVirtuallyNilpotentData.liftFiniteKernel
    (D : AscendingVirtuallyNilpotentData Q)
    (q : G →* Q) (hq : Function.Surjective q) [Finite q.ker] :
    AscendingVirtuallyNilpotentData G := by
  let h := D.height.comp q
  let t := (hq D.letter).choose
  have ht : q t = D.letter := (hq D.letter).choose_spec
  let f : h.ker →* D.height.ker :=
    (q.comp h.ker.subtype).codRestrict D.height.ker (fun g => g.property)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := hq x
    have hgker : g ∈ h.ker := by
      change D.height (q g) = 1
      rw [hg]
      exact x.property
    exact ⟨⟨g, hgker⟩, Subtype.ext hg⟩
  let k : f.ker → q.ker := fun c => ⟨((c : h.ker) : G), by
    change q ((c : h.ker) : G) = 1
    exact congrArg (fun b : D.height.ker => (b : Q)) c.property⟩
  have hk : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : q.ker => (c : G)) hab
  let : Finite f.ker := Finite.of_injective k hk
  let B := D.base.comap f
  have hBfg : B.FG := fg_preimage_of_finite_kernel f hf D.base
    ((Group.fg_iff_subgroup_fg D.base).mp D.base_fg)
  have hconj (g : h.ker) :
      f (MulAut.conjNormal (H := h.ker) t g) =
        MulAut.conjNormal (H := D.height.ker) D.letter (f g) := by
    apply Subtype.ext
    change q (t * (g : G) * t⁻¹) = D.letter * q g * D.letter⁻¹
    rw [map_mul, map_mul, map_inv, ht]
  refine
    { height := h
      letter := t
      height_letter := by
        change D.height (q t) = _
        rw [ht, D.height_letter]
      base := B
      base_fg := (Group.fg_iff_subgroup_fg B).mpr hBfg
      base_nilpotent := virtuallyNilpotent_preimage_of_finite_kernel_of_virtuallyNilpotent
        f D.base D.base_nilpotent
      stable := ?_
      exhaustive := ?_ }
  · rintro _ ⟨g, hg, rfl⟩
    change f (MulAut.conjNormal (H := h.ker) t g) ∈ D.base
    rw [hconj]
    exact D.stable ⟨f g, hg, rfl⟩
  · intro g
    obtain ⟨n, hn⟩ := D.exhaustive (f g)
    refine ⟨n, (mem_automorphismStage_iff _ _ _ _).mpr ?_⟩
    change f (((MulAut.conjNormal (H := h.ker) t) ^ n) g) ∈ D.base
    rw [automorphism_pow_equivariant f _ _ hconj]
    exact (mem_automorphismStage_iff _ _ _ _).mp hn

theorem virtualSolvableFiniteDimension_of_finiteKernel_ascending
    (q : G →* Q) (hq : Function.Surjective q) [Finite q.ker]
    (D : AscendingVirtuallyNilpotentData Q) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V :=
  (D.liftFiniteKernel q hq).virtualSolvableFiniteDimension

end PolycyclicRecognition

end

end OAI
