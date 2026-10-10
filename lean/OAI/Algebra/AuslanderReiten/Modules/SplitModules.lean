import OAI.Algebra.AuslanderReiten.Complete.CompleteResolution
import Mathlib.Algebra.Module.Injective

namespace OAI

noncomputable section

namespace ArExplicit

universe u

variable {R M N : Type u} [Ring R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

theorem finiteProjective_injective [Module.Injective R R]
    [Module.Finite R M] [Module.Projective R M] : Module.Injective R M where
  out := by
    intro X Y _ _ _ _ f hf g
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
    obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
    obtain ⟨g', hg'⟩ := Module.Injective.extension_property R (Fin n → R) X Y f hf (s.comp g)
    refine ⟨p.comp g', ?_⟩
    intro x
    change p (g' (f x)) = g x
    rw [show g' (f x) = s (g x) from DFunLike.congr_fun hg' x]
    exact DFunLike.congr_fun hs (g x)

def splitKernelProjection (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hs : f.comp s = LinearMap.id) :
    M →ₗ[R] LinearMap.ker f :=
  (LinearMap.id - s.comp f).codRestrict _ (by
    intro x
    change f (x - s (f x)) = 0
    rw [map_sub, show f (s (f x)) = f x from DFunLike.congr_fun hs (f x)]
    exact sub_self _)

@[simp] theorem splitKernelProjection_subtype (f : M →ₗ[R] N) (s : N →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) :
    (splitKernelProjection f s hs).comp (LinearMap.ker f).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [splitKernelProjection, show f x.val = 0 from x.property]

theorem projective_kernel_of_surjective [Module.Projective R M] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Projective R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f (LinearMap.id : N →ₗ[R] N) hf
  exact Module.Projective.of_split (LinearMap.ker f).subtype (splitKernelProjection f s hs)
    (splitKernelProjection_subtype f s hs)

theorem finite_kernel_of_surjective [Module.Finite R M] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Finite R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f (LinearMap.id : N →ₗ[R] N) hf
  apply Module.Finite.of_surjective (splitKernelProjection f s hs)
  intro x
  exact ⟨x.val, DFunLike.congr_fun (splitKernelProjection_subtype f s hs) x⟩

def splitCokernelSection (i : M →ₗ[R] N) (r : N →ₗ[R] M) (hr : r.comp i = LinearMap.id) :
    (N ⧸ LinearMap.range i) →ₗ[R] N :=
  (LinearMap.range i).liftQ (LinearMap.id - i.comp r) (by
    rintro x ⟨m, rfl⟩
    change i m - i (r (i m)) = 0
    rw [show r (i m) = m from DFunLike.congr_fun hr m]
    exact sub_self _)

@[simp] theorem splitCokernelSection_mkQ (i : M →ₗ[R] N) (r : N →ₗ[R] M)
    (hr : r.comp i = LinearMap.id) :
    (LinearMap.range i).mkQ.comp (splitCokernelSection i r hr) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range i) x
  change (LinearMap.range i).mkQ (x - i (r x)) = (LinearMap.range i).mkQ x
  rw [map_sub]
  have hi : (LinearMap.range i).mkQ (i (r x)) = 0 :=
    DFunLike.congr_fun (LinearMap.range_mkQ_comp i) (r x)
  rw [hi, sub_zero]

theorem projective_cokernel_of_injective [Module.Injective R M] [Module.Projective R N]
    (i : M →ₗ[R] N) (hi : Function.Injective i) : Module.Projective R (N ⧸ LinearMap.range i) := by
  obtain ⟨r, hr⟩ := Module.Injective.extension_property R M M N i hi (LinearMap.id : M →ₗ[R] M)
  exact Module.Projective.of_split (splitCokernelSection i r hr) (LinearMap.range i).mkQ
    (splitCokernelSection_mkQ i r hr)

end ArExplicit

end

end OAI
