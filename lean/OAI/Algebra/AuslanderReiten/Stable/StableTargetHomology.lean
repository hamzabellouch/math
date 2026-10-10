import OAI.Algebra.AuslanderReiten.Stable.StableHomology

namespace OAI

namespace ArExplicit.StableTargetHomology

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P₁ P₀ Pminus N : Type u}
variable [AddCommGroup P₁] [Module R P₁] [Module k P₁] [IsScalarTower k R P₁]
variable [AddCommGroup P₀] [Module R P₀] [Module k P₀] [IsScalarTower k R P₀]
variable [AddCommGroup Pminus] [Module R Pminus] [Module k Pminus] [IsScalarTower k R Pminus]
variable [AddCommGroup N] [Module R N]

def postcomp {L M : Type u} [AddCommGroup L] [Module R L] [Module k L]
    [IsScalarTower k R L] [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] (f : L →ₗ[R] M) : (N →ₗ[R] L) →ₗ[k] (N →ₗ[R] M) where
  toFun g := f.comp g
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' _ _ := LinearMap.comp_smul _ _ _

theorem postcomp_comp (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0) :
    (postcomp (k := k) (N := N) d).comp (postcomp e) = 0 := by
  ext f x
  exact DFunLike.congr_fun h (f x)

def cycleToMap (d : P₀ →ₗ[R] Pminus)
    (z : LinearMap.ker (postcomp (k := k) (N := N) d)) : N →ₗ[R] LinearMap.ker d :=
  z.val.codRestrict _ (fun x => DFunLike.congr_fun z.property x)

def cyclesToStable (d : P₀ →ₗ[R] Pminus) :
    LinearMap.ker (postcomp (k := k) (N := N) d) →ₗ[k] StableHom R N (LinearMap.ker d) where
  toFun z := StableHom.classOf R _ _ (cycleToMap d z)
  map_add' z w := by
    have he : cycleToMap d (z + w) = cycleToMap d z + cycleToMap d w := by ext; rfl
    rw [he, map_add]
  map_smul' c z := by
    have he : cycleToMap d (c • z) = c • cycleToMap d z := by ext; rfl
    rw [he, StableHom.classOf_smul]
    rfl

theorem cyclesToStable_surjective (d : P₀ →ₗ[R] Pminus) :
    Function.Surjective (cyclesToStable (k := k) (N := N) d) := by
  intro x
  obtain ⟨f, rfl⟩ := StableHom.classOf_surjective x
  have hz : (LinearMap.ker d).subtype.comp f ∈ LinearMap.ker (postcomp (k := k) d) := by
    ext y
    exact (f y).property
  refine ⟨⟨(LinearMap.ker d).subtype.comp f, hz⟩, ?_⟩
  apply congrArg (StableHom.classOf R N (LinearMap.ker d))
  ext
  rfl

theorem cyclesToStable_kernel [Module.Finite R P₁] [Module.Projective R P₁]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hex : LinearMap.range e = LinearMap.ker d) :
    LinearMap.ker (cyclesToStable (k := k) (N := N) d) =
      LinearHomology.boundaries (postcomp e) (postcomp d) (postcomp_comp e d h) := by
  ext z
  constructor
  · intro hz
    change StableHom.classOf R N (LinearMap.ker d) (cycleToMap d z) = 0 at hz
    rcases (StableHom.classOf_eq_zero_iff_projective (cycleToMap d z)).mp hz with
      ⟨T, hT, hRT, hpT, hfT, a, b, hab⟩
    have hb : d.comp ((LinearMap.ker d).subtype.comp b) = 0 := by
      ext x
      exact (b x).property
    obtain ⟨B, hB⟩ := lift_through_exact e d hex ((LinearMap.ker d).subtype.comp b) hb
    refine ⟨B.comp a, ?_⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change e (B (a x)) = z.val x
    rw [show e (B (a x)) = (b (a x)).val from DFunLike.congr_fun hB (a x)]
    exact congrArg Subtype.val (DFunLike.congr_fun hab x)
  · rintro ⟨a, rfl⟩
    apply (StableHom.classOf_eq_zero_iff_projective _).mpr
    refine ⟨P₁, inferInstance, inferInstance, inferInstance, inferInstance,
      a, e.codRestrict (LinearMap.ker d) (fun x => DFunLike.congr_fun h x), ?_⟩
    ext
    rfl

noncomputable def homologyStableEquiv [Module.Finite R P₁] [Module.Projective R P₁]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hex : LinearMap.range e = LinearMap.ker d) :
    LinearHomology.Homology (postcomp (k := k) (N := N) e) (postcomp d) (postcomp_comp e d h)
      ≃ₗ[k] StableHom R N (LinearMap.ker d) :=
  (Submodule.quotEquivOfEq _ _ (cyclesToStable_kernel e d h hex).symm).trans
    ((cyclesToStable d).quotKerEquivOfSurjective (cyclesToStable_surjective d))

@[simp]
theorem homologyStableEquiv_mk [Module.Finite R P₁] [Module.Projective R P₁]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hex : LinearMap.range e = LinearMap.ker d)
    (z : LinearMap.ker (postcomp (k := k) (N := N) d)) :
    homologyStableEquiv e d h hex
      ((LinearHomology.boundaries (postcomp e) (postcomp d) (postcomp_comp e d h)).mkQ z) =
      cyclesToStable d z := rfl

def mapToCycle (d : P₀ →ₗ[R] Pminus) (f : N →ₗ[R] LinearMap.ker d) :
    LinearMap.ker (postcomp (k := k) (N := N) d) :=
  ⟨(LinearMap.ker d).subtype.comp f, by ext x; exact (f x).property⟩

@[simp]
theorem cyclesToStable_mapToCycle (d : P₀ →ₗ[R] Pminus) (f : N →ₗ[R] LinearMap.ker d) :
    cyclesToStable d (mapToCycle (k := k) d f) = StableHom.classOf R _ _ f := by
  apply congrArg (StableHom.classOf R N (LinearMap.ker d))
  ext
  rfl

end ArExplicit.StableTargetHomology

end OAI
