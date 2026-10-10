import OAI.Algebra.AuslanderReiten.Cones.ConeExactness
import OAI.Algebra.AuslanderReiten.Stable.StableIsomorphism

namespace OAI

namespace ArExplicit.ConeQuotientMap

universe u

variable {R P₁ P₀ I Q₁ Q₀ L : Type u} [Ring R]
variable [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₀] [Module R P₀]
variable [AddCommGroup I] [Module R I] [AddCommGroup Q₁] [Module R Q₁]
variable [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup L] [Module R L]

variable (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] I) (b : Q₁ →ₗ[R] Q₀) (f : P₀ →ₗ[R] Q₀)

abbrev Source := P₀ ⧸ LinearMap.range e
abbrev Target := Q₀ ⧸ LinearMap.range b
abbrev Cone := (Q₀ × I) ⧸ LinearMap.range (coneBlock b d f)

variable (i : Source e →ₗ[R] Target b)
variable (p : Target b →ₗ[R] L)
variable (hf : (LinearMap.range b).mkQ.comp f = i.comp (LinearMap.range e).mkQ)
variable (hex : Function.Exact i p)

def kernelInclusion : I →ₗ[R] Cone d b f :=
  (LinearMap.range (coneBlock b d f)).mkQ.comp (LinearMap.inr R Q₀ I)

def quotientMap : Cone d b f →ₗ[R] L :=
  (LinearMap.range (coneBlock b d f)).liftQ
    ((p.comp (LinearMap.range b).mkQ).comp (LinearMap.fst R Q₀ I)) (by
      rintro _ ⟨⟨q, x⟩, rfl⟩
      change p ((LinearMap.range b).mkQ (b q + f x)) = 0
      rw [map_add, show (LinearMap.range b).mkQ (b q) = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨q, rfl⟩, zero_add]
      rw [show (LinearMap.range b).mkQ (f x) = i ((LinearMap.range e).mkQ x) from
        DFunLike.congr_fun hf x]
      exact (hex _).mpr ⟨_, rfl⟩)

@[simp]
theorem quotientMap_mk (x : Q₀) (y : I) :
    quotientMap e d b f i p hf hex (Submodule.Quotient.mk (x, y)) =
      p (Submodule.Quotient.mk x) := rfl

@[simp]
theorem kernelInclusion_apply (y : I) :
    kernelInclusion d b f y = Submodule.Quotient.mk (0, y) := rfl

include hf in

theorem kernelInclusion_injective (hi : Function.Injective i)
    (hed : d.comp e = 0) : Function.Injective (kernelInclusion d b f) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro y hy
  obtain ⟨⟨q, x⟩, hqx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
  have hx : i ((LinearMap.range e).mkQ x) = 0 := by
    have h := congrArg ((LinearMap.range b).mkQ) (congrArg Prod.fst hqx)
    change (LinearMap.range b).mkQ (b q + f x) = (LinearMap.range b).mkQ 0 at h
    rw [map_add, show (LinearMap.range b).mkQ (b q) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨q, rfl⟩, zero_add, map_zero] at h
    rw [show (LinearMap.range b).mkQ (f x) = i ((LinearMap.range e).mkQ x) from
      DFunLike.congr_fun hf x] at h
    exact h
  have hx0 : (LinearMap.range e).mkQ x = 0 := hi (by simpa only [map_zero] using hx)
  obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx0
  have hy' := congrArg Prod.snd hqx
  change -d x = y at hy'
  rw [← hz, show d (e z) = 0 from DFunLike.congr_fun hed z, neg_zero] at hy'
  exact hy'.symm

theorem quotientMap_surjective (hp : Function.Surjective p) :
    Function.Surjective (quotientMap e d b f i p hf hex) := by
  intro z
  obtain ⟨x, rfl⟩ := hp z
  obtain ⟨x, rfl⟩ := (LinearMap.range b).mkQ_surjective x
  exact ⟨Submodule.Quotient.mk (x, 0), rfl⟩

theorem exact : Function.Exact (kernelInclusion d b f) (quotientMap e d b f i p hf hex) := by
  intro z
  obtain ⟨⟨q, y⟩, rfl⟩ := (LinearMap.range (coneBlock b d f)).mkQ_surjective z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := (hex ((LinearMap.range b).mkQ q)).mp hz
    obtain ⟨x, rfl⟩ := (LinearMap.range e).mkQ_surjective x
    have hb : q - f x ∈ LinearMap.range b := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change (LinearMap.range b).mkQ (q - f x) = 0
      rw [map_sub, show (LinearMap.range b).mkQ (f x) = i ((LinearMap.range e).mkQ x) from
        DFunLike.congr_fun hf x, hx, sub_self]
    obtain ⟨q', hq'⟩ := hb
    refine ⟨y + d x, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨(-q', -x), ?_⟩
    apply Prod.ext
    · change b (-q') + f (-x) = 0 - q
      rw [map_neg, map_neg, hq']
      abel
    · change -d (-x) = (y + d x) - y
      rw [map_neg, neg_neg]
      abel
  · rintro ⟨y', hy'⟩
    rw [← hy']
    change p ((LinearMap.range b).mkQ 0) = 0
    simp

noncomputable def stableIsomorphism
    [Module.Finite R I] [Module.Projective R I] [Module.Injective R I]
    (hi : Function.Injective i) (hed : d.comp e = 0) (hp : Function.Surjective p) :
    StableIsomorphism R (Cone d b f) L :=
  StableIsomorphism.ofExactProjectiveKernel (kernelInclusion d b f)
    (quotientMap e d b f i p hf hex) (kernelInclusion_injective e d b f i hf hi hed)
    (quotientMap_surjective e d b f i p hf hex hp) (exact e d b f i p hf hex)

end ArExplicit.ConeQuotientMap

end OAI
