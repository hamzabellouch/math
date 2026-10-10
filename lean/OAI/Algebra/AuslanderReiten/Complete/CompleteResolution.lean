import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic

namespace OAI

namespace ArExplicit

universe u v w x y z

variable {R : Type u} [Ring R]
variable {K : Type v} [AddCommGroup K] [Module R K]
variable {L : Type w} [AddCommGroup L] [Module R L]
variable {M : Type x} [AddCommGroup M] [Module R M]
variable {Q : Type y} [AddCommGroup Q] [Module R Q]

def HomExactAt (e : K →ₗ[R] L) (d : L →ₗ[R] M) : Prop :=
  ∀ f : L →ₗ[R] R, f.comp e = 0 → ∃ g : M →ₗ[R] R, g.comp d = f

namespace HomExactAt

variable {e : K →ₗ[R] L} {d : L →ₗ[R] M}

theorem projective [Module.Finite R Q] [Module.Projective R Q]
    (h : HomExactAt e d) (f : L →ₗ[R] Q) (hf : f.comp e = 0) :
    ∃ g : M →ₗ[R] Q, g.comp d = f := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R Q
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π (LinearMap.id : Q →ₗ[R] Q) hπ
  have coordinate_exists (i : Fin n) :
      ∃ g : M →ₗ[R] R, g.comp d = (LinearMap.proj i).comp (s.comp f) := by
    apply h
    ext z
    change (s (f (e z))) i = 0
    rw [show f (e z) = 0 from DFunLike.congr_fun hf z, map_zero]
    rfl
  choose g hg using coordinate_exists
  let G : M →ₗ[R] (Fin n → R) := LinearMap.pi g
  refine ⟨π.comp G, ?_⟩
  ext z
  have hz : G (d z) = s (f z) := by
    funext i
    exact DFunLike.congr_fun (hg i) z
  change π (G (d z)) = f z
  rw [hz]
  exact DFunLike.congr_fun hs (f z)

theorem extend_range [Module.Finite R Q] [Module.Projective R Q]
    (h : HomExactAt e d) (hde : d.comp e = 0)
    (f : LinearMap.range d →ₗ[R] Q) :
    ∃ g : M →ₗ[R] Q, g.comp (LinearMap.range d).subtype = f := by
  have hf : (f.comp d.rangeRestrict).comp e = 0 := by
    ext z
    have hz : d.rangeRestrict (e z) = 0 := by
      apply Subtype.ext
      exact DFunLike.congr_fun hde z
    change f (d.rangeRestrict (e z)) = 0
    rw [hz, map_zero]
  obtain ⟨g, hg⟩ := h.projective (f.comp d.rangeRestrict) hf
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := d.surjective_rangeRestrict z
  exact DFunLike.congr_fun hg z

theorem extend_kernel {N : Type z} [AddCommGroup N] [Module R N]
    [Module.Finite R Q] [Module.Projective R Q]
    (h : HomExactAt e d) (hde : d.comp e = 0)
    (d' : M →ₗ[R] N) (hex : LinearMap.range d = LinearMap.ker d')
    (f : LinearMap.ker d' →ₗ[R] Q) :
    ∃ g : M →ₗ[R] Q, g.comp (LinearMap.ker d').subtype = f := by
  obtain ⟨g, hg⟩ := h.extend_range hde (f.comp (Submodule.inclusion hex.le))
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro t
  have ht : (t : M) ∈ LinearMap.range d := by
    rw [hex]
    exact t.property
  exact DFunLike.congr_fun hg ⟨t, ht⟩

end HomExactAt

section ProjectiveLifting

theorem lift_through_exact [Module.Projective R Q]
    (e : K →ₗ[R] L) (d : L →ₗ[R] M)
    (hex : LinearMap.range e = LinearMap.ker d)
    (f : Q →ₗ[R] L) (hf : d.comp f = 0) :
    ∃ g : Q →ₗ[R] K, e.comp g = f := by
  let f' : Q →ₗ[R] LinearMap.range e := f.codRestrict _ (by
    intro q
    rw [hex]
    exact DFunLike.congr_fun hf q)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property e.rangeRestrict f'
    e.surjective_rangeRestrict
  refine ⟨g, ?_⟩
  ext q
  exact congrArg Subtype.val (DFunLike.congr_fun hg q)

theorem lift_cokernel_map [Module.Projective R K] [Module.Projective R L]
    (e : K →ₗ[R] L) (d : M →ₗ[R] Q)
    (u : (L ⧸ LinearMap.range e) →ₗ[R] (Q ⧸ LinearMap.range d)) :
    ∃ (f₀ : L →ₗ[R] Q) (f₁ : K →ₗ[R] M),
      (LinearMap.range d).mkQ.comp f₀ = u.comp (LinearMap.range e).mkQ ∧
      d.comp f₁ = f₀.comp e := by
  obtain ⟨f₀, hf₀⟩ := Module.projective_lifting_property (LinearMap.range d).mkQ
    (u.comp (LinearMap.range e).mkQ) (Submodule.mkQ_surjective _)
  have hz : (LinearMap.range d).mkQ.comp (f₀.comp e) = 0 := by
    ext q
    change (LinearMap.range d).mkQ (f₀ (e q)) = 0
    calc
      (LinearMap.range d).mkQ (f₀ (e q)) =
          u ((LinearMap.range e).mkQ (e q)) := DFunLike.congr_fun hf₀ (e q)
      _ = 0 := by
        rw [show (LinearMap.range e).mkQ (e q) = 0 by
          exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨q, rfl⟩, map_zero]
  obtain ⟨f₁, hf₁⟩ := lift_through_exact d (LinearMap.range d).mkQ
    (Submodule.ker_mkQ _).symm (f₀.comp e) hz
  exact ⟨f₀, f₁, hf₀, hf₁⟩

end ProjectiveLifting

section ComparisonSteps

universe a b c

variable {U : Type a} [AddCommGroup U] [Module R U]
variable {V : Type b} [AddCommGroup V] [Module R V]
variable {W : Type c} [AddCommGroup W] [Module R W]

theorem extend_comparison_up [Module.Projective R K]
    (e : K →ₗ[R] L) (d : L →ₗ[R] M) (hde : d.comp e = 0)
    (e' : U →ₗ[R] V) (d' : V →ₗ[R] W)
    (hex : LinearMap.range e' = LinearMap.ker d')
    (f : L →ₗ[R] V) (g : M →ₗ[R] W) (hfg : d'.comp f = g.comp d) :
    ∃ h : K →ₗ[R] U, e'.comp h = f.comp e := by
  apply lift_through_exact e' d' hex (f.comp e)
  ext t
  change d' (f (e t)) = 0
  calc
    d' (f (e t)) = g (d (e t)) := DFunLike.congr_fun hfg (e t)
    _ = 0 := by rw [show d (e t) = 0 from DFunLike.congr_fun hde t, map_zero]

theorem extend_comparison_down [Module.Finite R W] [Module.Projective R W]
    (e : K →ₗ[R] L) (d : L →ₗ[R] M) (hdual : HomExactAt e d)
    (e' : U →ₗ[R] V) (d' : V →ₗ[R] W) (hde' : d'.comp e' = 0)
    (f : K →ₗ[R] U) (g : L →ₗ[R] V) (hfg : e'.comp f = g.comp e) :
    ∃ h : M →ₗ[R] W, h.comp d = d'.comp g := by
  apply hdual.projective (d'.comp g)
  ext t
  change d' (g (e t)) = 0
  calc
    d' (g (e t)) = d' (e' (f t)) := congrArg d' (DFunLike.congr_fun hfg t).symm
    _ = 0 := DFunLike.congr_fun hde' (f t)

end ComparisonSteps

end ArExplicit

end OAI
