import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Topology.Algebra.MulAction

namespace OAI

/-! # Descending automorphisms through an actual surjective group map -/

noncomputable section
namespace PolycyclicRecognition

variable {N Q D : Type*} [Group N] [Group Q] [Group D]

/-- A kernel-preserving automorphism descends using any section of the
surjective quotient map. Its value on a projected point is independent of
the choice of section. -/
def descendQuotientAutomorphism (π : N →* Q) (s : Q → N)
    (hs : Function.RightInverse s π) (e : N ≃* N)
    (he : ∀ n, e n ∈ π.ker ↔ n ∈ π.ker) : Q ≃* Q := by
  let f : Q →* Q := π.liftOfRightInverse s hs
    ⟨π.comp e.toMonoidHom, fun n hn => (he n).mpr hn⟩
  let g : Q →* Q := π.liftOfRightInverse s hs
    ⟨π.comp e.symm.toMonoidHom, fun n hn => by
      have h := (he (e.symm n)).mp
      exact h (by simpa using hn)⟩
  have hf (n) : f (π n) = π (e n) := π.liftOfRightInverse_comp_apply s hs _ n
  have hg (n) : g (π n) = π (e.symm n) := π.liftOfRightInverse_comp_apply s hs _ n
  exact
    { f with
      invFun := g
      left_inv := fun q => by
        obtain ⟨n, rfl⟩ := hs.surjective q
        change g (f (π n)) = π n
        rw [hf, hg, e.symm_apply_apply]
      right_inv := fun q => by
        obtain ⟨n, rfl⟩ := hs.surjective q
        change f (g (π n)) = π n
        rw [hg, hf, e.apply_symm_apply] }

@[simp] theorem descendQuotientAutomorphism_project
    (π : N →* Q) (s : Q → N) (hs : Function.RightInverse s π) (e : N ≃* N)
    (he : ∀ n, e n ∈ π.ker ↔ n ∈ π.ker) (n : N) :
    descendQuotientAutomorphism π s hs e he (π n) = π (e n) := by
  change π (e (s (π n))) = π (e n)
  exact π.liftOfRightInverseAux_comp_apply s hs (π.comp e.toMonoidHom)
    (fun x hx => (he x).mpr hx) n

/-- A group of automorphisms preserving the kernel acts on the quotient. -/
def descendQuotientAction (π : N →* Q) (s : Q → N)
    (hs : Function.RightInverse s π) (a : D →* MulAut N)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker) : D →* MulAut Q where
  toFun d := descendQuotientAutomorphism π s hs (a d) (ha d)
  map_one' := by
    ext q
    obtain ⟨n, rfl⟩ := hs.surjective q
    simp only [descendQuotientAutomorphism_project, map_one, MulAut.one_apply]
  map_mul' d e := by
    ext q
    obtain ⟨n, rfl⟩ := hs.surjective q
    simp only [descendQuotientAutomorphism_project, map_mul, MulAut.mul_apply]

@[simp] theorem descendQuotientAction_project
    (π : N →* Q) (s : Q → N) (hs : Function.RightInverse s π) (a : D →* MulAut N)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker) (d : D) (n : N) :
    descendQuotientAction π s hs a ha d (π n) = π (a d n) :=
  descendQuotientAutomorphism_project π s hs (a d) (ha d) n

/-- A continuous section makes each descended automorphism continuous as
soon as the original automorphism and quotient map are continuous. -/
theorem continuous_descendQuotientAutomorphism
    [TopologicalSpace N] [TopologicalSpace Q]
    (π : N →* Q) (s : Q → N) (hs : Function.RightInverse s π) (e : N ≃* N)
    (he : ∀ n, e n ∈ π.ker ↔ n ∈ π.ker)
    (hπ : Continuous π) (hscont : Continuous s) (hecont : Continuous e) :
    Continuous (descendQuotientAutomorphism π s hs e he) :=
  hπ.comp (hecont.comp hscont)

end PolycyclicRecognition

end

end OAI
