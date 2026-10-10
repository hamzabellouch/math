import Mathlib
import OAI.Geometry.HyperbolicGroups.HSpacePathObstruction

namespace OAI

/-! Reversing the spatial coordinate of an actual two-loop negates its genuine
fundamental class in the compact-open loop space. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.LoopSpaceReversal
variable {X : Type*} [TopologicalSpace X] (b : X)
local notation "e" => (Path.refl b)
local notation "Q" => Path.Homotopic.Quotient.mk

def reverse (u : Path e e) : Path e e :=
  (u.map Path.continuous_symm).cast Path.refl_symm.symm Path.refl_symm.symm

@[simp] lemma reverse_apply (u : Path e e) (t s : I) : reverse b u t s = u t (unitInterval.symm s) := rfl

/-- The cancellation homotopy is continuous jointly in both parameters and
in the loop itself. -/
def cancel (u : Path e e) : (Path.refl e).Homotopy
    (HSpaceFundamental.combinePath u (reverse b u)) where
  toFun tx := (Path.Homotopy.reflTransSymm (u tx.2)).eval tx.1
  continuous_toFun := Path.continuous_uncurry_iff.mp (by
    change Continuous (fun z : (I × I) × I =>
      u z.1.2 ⟨Path.Homotopy.reflTransSymmAux (z.1.1,z.2),
        Path.Homotopy.reflTransSymmAux_mem_I (z.1.1,z.2)⟩)
    exact (Path.continuous_uncurry_iff.mpr u.continuous).comp
      ((continuous_snd.comp continuous_fst).prodMk
        ((Path.Homotopy.continuous_reflTransSymmAux.comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).subtype_mk _)))
  map_zero_left := by intro t; ext s; simp [Path.Homotopy.reflTransSymm]
  map_one_left := by
    intro t
    change (Path.Homotopy.reflTransSymm (u t)).eval 1 = _
    rw [Path.Homotopy.eval_one]
    rfl
  prop' := by
    intro t s hs
    rcases hs with hs|hs
    · subst s; ext r; simp [Path.Homotopy.reflTransSymm]; rfl
    · simp only [Set.mem_singleton_iff] at hs
      subst s; ext r; simp [Path.Homotopy.reflTransSymm]; rfl

lemma reverse_class (u : Path e e) :
    HSpacePathObstruction.loopClass (reverse b u) = (HSpacePathObstruction.loopClass u)⁻¹ := by
  have hh := Path.Homotopic.Quotient.eq.mpr (Nonempty.intro (cancel b u))
  have hz : HSpacePathObstruction.loopClass u * HSpacePathObstruction.loopClass (reverse b u) = 1 := by
    rw [←HSpacePathObstruction.loopClass_combine]
    exact hh.symm
  exact eq_inv_of_mul_eq_one_right hz

end HyperbolicObstruction.LoopSpaceReversal
end

end OAI
