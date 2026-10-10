import Mathlib

namespace OAI

section


/-! The genuine compact-open path space realizes relative homotopies as paths.
This is the two-dimensional path-space interface used for cellular obstructions. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.PathHomotopyTopology
variable {X : Type*} [TopologicalSpace X] {a b : X} {p q : Path a b}

def fromHomotopy (H : p.Homotopy q) : Path p q where
  toFun := H.eval
  continuous_toFun := Path.continuous_uncurry_iff.mp H.continuous
  source' := H.eval_zero
  target' := H.eval_one

def toHomotopy (P : Path p q) : p.Homotopy q where
  toFun tx := P tx.1 tx.2
  continuous_toFun := Path.continuous_uncurry_iff.mpr P.continuous
  map_zero_left x := by simp
  map_one_left x := by simp
  prop' t x hx := by
    rcases hx with hx|hx
    · subst x; simp
    · simp only [Set.mem_singleton_iff] at hx
      subst x; simp

@[simp] lemma fromHomotopy_apply (H : p.Homotopy q) (t s : I) :
    fromHomotopy H t s = H (t,s) := rfl
@[simp] lemma toHomotopy_apply (P : Path p q) (t s : I) :
    toHomotopy P (t,s) = P t s := rfl

/-- No homotopy classes are collapsed by this change of representation. -/
def equiv : (p.Homotopy q) ≃ Path p q where
  toFun := fromHomotopy
  invFun := toHomotopy
  left_inv H := by ext tx; rfl
  right_inv P := by ext t s; rfl

lemma joined_iff_homotopic : Joined p q ↔ p.Homotopic q := by
  exact ⟨fun h => h.somePath |> toHomotopy |> Nonempty.intro,
    fun ⟨H⟩ => ⟨fromHomotopy H⟩⟩

end HyperbolicObstruction.PathHomotopyTopology
end
end

section

end

end OAI
