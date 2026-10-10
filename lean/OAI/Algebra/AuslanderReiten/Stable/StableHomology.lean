import OAI.Algebra.AuslanderReiten.Duality.LinearHomologyDuality
import OAI.Algebra.AuslanderReiten.Complete.CompleteResolution
import OAI.Algebra.AuslanderReiten.Stable.StableHom

namespace OAI

namespace ArExplicit.StableHomology

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P₁ P₀ Pminus N : Type u}
variable [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₀] [Module R P₀]
variable [AddCommGroup Pminus] [Module R Pminus] [AddCommGroup N] [Module R N]
variable [Module k N] [IsScalarTower k R N]

def precomp {L M : Type u} [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    (f : L →ₗ[R] M) : (M →ₗ[R] N) →ₗ[k] (L →ₗ[R] N) where
  toFun g := g.comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem precomp_comp (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0) :
    (precomp (k := k) (N := N) e).comp (precomp d) = 0 := by
  ext f x
  change f (d (e x)) = 0
  rw [show d (e x) = 0 from DFunLike.congr_fun h x, map_zero]

abbrev Cokernel (e : P₁ →ₗ[R] P₀) := P₀ ⧸ LinearMap.range e

def cycleToMap (e : P₁ →ₗ[R] P₀)
    (z : LinearMap.ker (precomp (k := k) (N := N) e)) : Cokernel e →ₗ[R] N :=
  (LinearMap.range e).liftQ z.val (by
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun z.property x)

@[simp]
theorem cycleToMap_mkQ (e : P₁ →ₗ[R] P₀)
    (z : LinearMap.ker (precomp (k := k) (N := N) e)) (x : P₀) :
    cycleToMap e z ((LinearMap.range e).mkQ x) = z.val x := rfl

def cyclesToStable (e : P₁ →ₗ[R] P₀) :
    LinearMap.ker (precomp (k := k) (N := N) e) →ₗ[k] StableHom R (Cokernel e) N where
  toFun z := StableHom.classOf R _ _ (cycleToMap e z)
  map_add' z w := by
    have he : cycleToMap e (z + w) = cycleToMap e z + cycleToMap e w := by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) x
      rfl
    rw [he, map_add]
  map_smul' c z := by
    have he : cycleToMap e (c • z) = c • cycleToMap e z := by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) x
      rfl
    rw [he, StableHom.classOf_smul]
    rfl

theorem cyclesToStable_surjective (e : P₁ →ₗ[R] P₀) :
    Function.Surjective (cyclesToStable (k := k) (N := N) e) := by
  intro x
  obtain ⟨f, rfl⟩ := StableHom.classOf_surjective x
  have hz : f.comp (LinearMap.range e).mkQ ∈ LinearMap.ker (precomp (k := k) e) := by
    ext y
    change f ((LinearMap.range e).mkQ (e y)) = 0
    rw [show (LinearMap.range e).mkQ (e y) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩, map_zero]
  refine ⟨⟨f.comp (LinearMap.range e).mkQ, hz⟩, ?_⟩
  apply congrArg (StableHom.classOf R (Cokernel e) N)
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) x
  rfl

theorem cyclesToStable_kernel [Module.Finite R Pminus] [Module.Projective R Pminus]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hd : HomExactAt e d) :
    LinearMap.ker (cyclesToStable (k := k) (N := N) e) =
      LinearHomology.boundaries (precomp d) (precomp e) (precomp_comp e d h) := by
  ext z
  constructor
  · intro hz
    change StableHom.classOf R (Cokernel e) N (cycleToMap e z) = 0 at hz
    rcases (StableHom.classOf_eq_zero_iff_projective (cycleToMap e z)).mp hz with
      ⟨T, hT, hRT, hpT, hfT, a, b, hab⟩
    have ha : (a.comp (LinearMap.range e).mkQ).comp e = 0 := by
      ext x
      change a ((LinearMap.range e).mkQ (e x)) = 0
      rw [show (LinearMap.range e).mkQ (e x) = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero]
    obtain ⟨A, hA⟩ := hd.projective (a.comp (LinearMap.range e).mkQ) ha
    refine ⟨b.comp A, ?_⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change b (A (d x)) = z.val x
    rw [show A (d x) = a ((LinearMap.range e).mkQ x) from DFunLike.congr_fun hA x]
    exact DFunLike.congr_fun hab ((LinearMap.range e).mkQ x)
  · rintro ⟨b, rfl⟩
    apply (StableHom.classOf_eq_zero_iff_projective _).mpr
    have he : LinearMap.range e ≤ LinearMap.ker d := LinearMap.range_le_ker_iff.mpr h
    refine ⟨Pminus, inferInstance, inferInstance, inferInstance, inferInstance,
      (LinearMap.range e).liftQ d he, b, ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) x
    rfl

noncomputable def homologyStableEquiv [Module.Finite R Pminus] [Module.Projective R Pminus]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hd : HomExactAt e d) :
    LinearHomology.Homology (precomp (k := k) (N := N) d) (precomp e) (precomp_comp e d h)
      ≃ₗ[k] StableHom R (Cokernel e) N :=
  (Submodule.quotEquivOfEq _ _ (cyclesToStable_kernel e d h hd).symm).trans
    ((cyclesToStable e).quotKerEquivOfSurjective (cyclesToStable_surjective e))

@[simp]
theorem homologyStableEquiv_mk [Module.Finite R Pminus] [Module.Projective R Pminus]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hd : HomExactAt e d) (z : LinearMap.ker (precomp (k := k) (N := N) e)) :
    homologyStableEquiv e d h hd
      ((LinearHomology.boundaries (precomp d) (precomp e) (precomp_comp e d h)).mkQ z) =
      cyclesToStable e z := rfl

def mapToCycle (e : P₁ →ₗ[R] P₀) (f : Cokernel e →ₗ[R] N) :
    LinearMap.ker (precomp (k := k) (N := N) e) :=
  ⟨f.comp (LinearMap.range e).mkQ, by
    ext x
    change f ((LinearMap.range e).mkQ (e x)) = 0
    rw [show (LinearMap.range e).mkQ (e x) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero]⟩

@[simp]
theorem cyclesToStable_mapToCycle (e : P₁ →ₗ[R] P₀) (f : Cokernel e →ₗ[R] N) :
    cyclesToStable e (mapToCycle (k := k) e f) = StableHom.classOf R _ _ f := by
  apply congrArg (StableHom.classOf R (Cokernel e) N)
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) x
  rfl

end ArExplicit.StableHomology

end OAI
