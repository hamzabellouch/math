import OAI.Algebra.AuslanderReiten.Cones.TwoCone

namespace OAI

noncomputable section

namespace ArExplicit

variable {R M N E : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup E] [Module R E]

theorem projective_of_exact [Module.Projective R M] [Module.Projective R N]
    (i : M →ₗ[R] E) (p : E →ₗ[R] N) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) : Module.Projective R E := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : N →ₗ[R] N) hp
  have hpi (m : M) : p (i m) = 0 := (hex (i m)).mpr ⟨m, rfl⟩
  have hps (n : N) : p (s n) = n := DFunLike.congr_fun hs n
  apply Module.Projective.of_equiv (LinearEquiv.ofBijective (i.coprod s) ?_)
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨m,n⟩ h
    have hn : n = 0 := by
      have ht := congrArg p h
      simpa only [LinearMap.coprod_apply, map_add, hpi, hps, zero_add, map_zero] using ht
    subst n
    have hm : m = 0 := hi (by simpa using h)
    simp [hm]
  · intro e
    obtain ⟨m, hm⟩ := (hex (e - s (p e))).mp (by rw [map_sub, hps, sub_self])
    refine ⟨(m, p e), ?_⟩
    change i m + s (p e) = e
    rw [hm, sub_add_cancel]

namespace ConeCokernel

variable {Q₀ Q₁ P₀ P₁ P₂ : Type*}
variable [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup Q₁] [Module R Q₁]
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₂] [Module R P₂]
variable (dQ : Q₁ →ₗ[R] Q₀) (dP : P₁ →ₗ[R] P₀) (f : P₁ →ₗ[R] Q₀)

abbrev Left := Q₀ ⧸ LinearMap.range dQ
abbrev Right := P₀ ⧸ LinearMap.range dP
abbrev Middle := (Q₀ × P₀) ⧸ LinearMap.range (coneBlock dQ dP f)

def inclusion : Left dQ →ₗ[R] Middle dQ dP f :=
  (LinearMap.range dQ).liftQ
    ((LinearMap.range (coneBlock dQ dP f)).mkQ.comp (LinearMap.inl R Q₀ P₀)) (by
      rintro x ⟨a,rfl⟩
      change Submodule.Quotient.mk (dQ a, 0) = (0 : Middle dQ dP f)
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨(a,0), by simp⟩)

def projection : Middle dQ dP f →ₗ[R] Right dP :=
  (LinearMap.range (coneBlock dQ dP f)).liftQ
    ((LinearMap.range dP).mkQ.comp (LinearMap.snd R Q₀ P₀)) (by
      rintro x ⟨⟨a,b⟩,rfl⟩
      change Submodule.Quotient.mk (-dP b) = (0 : Right dP)
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨-b, map_neg dP b⟩)

@[simp] theorem inclusion_mk (x : Q₀) :
    inclusion dQ dP f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x,0) := rfl

@[simp] theorem projection_mk (x : Q₀) (y : P₀) :
    projection dQ dP f (Submodule.Quotient.mk (x,y)) = Submodule.Quotient.mk y := rfl

theorem projection_surjective : Function.Surjective (projection dQ dP f) := by
  intro y
  obtain ⟨y,rfl⟩ := (LinearMap.range dP).mkQ_surjective y
  exact ⟨Submodule.Quotient.mk (0,y), rfl⟩

theorem exact : Function.Exact (inclusion dQ dP f) (projection dQ dP f) := by
  intro z
  obtain ⟨⟨x,y⟩,rfl⟩ := (LinearMap.range (coneBlock dQ dP f)).mkQ_surjective z
  constructor
  · intro h
    have hy : y ∈ LinearMap.range dP := (Submodule.Quotient.mk_eq_zero _).mp h
    obtain ⟨b,hb⟩ := hy
    refine ⟨Submodule.Quotient.mk (x + f b), ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨(0,b), ?_⟩
    simp [coneBlock_apply, hb]
  · rintro ⟨w,hw⟩
    obtain ⟨w,rfl⟩ := (LinearMap.range dQ).mkQ_surjective w
    rw [← hw]
    exact Submodule.Quotient.mk_zero _

theorem inclusion_injective (eP : P₂ →ₗ[R] P₁) (f₁ : P₂ →ₗ[R] Q₁)
    (hex : Function.Exact eP dP) (hc : dQ.comp f₁ = f.comp eP) :
    Function.Injective (inclusion dQ dP f) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨x,rfl⟩ := (LinearMap.range dQ).mkQ_surjective z
  obtain ⟨⟨a,b⟩,hab⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hb : dP b = 0 := neg_eq_zero.mp (congrArg Prod.snd hab)
  obtain ⟨c,hc'⟩ := (hex b).mp hb
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨a + f₁ c, ?_⟩
  rw [map_add, show dQ (f₁ c) = f (eP c) from DFunLike.congr_fun hc c, hc']
  exact congrArg Prod.fst hab

theorem projective [Module.Projective R (Left dQ)] [Module.Projective R (Right dP)]
    (eP : P₂ →ₗ[R] P₁) (f₁ : P₂ →ₗ[R] Q₁)
    (hex : Function.Exact eP dP) (hc : dQ.comp f₁ = f.comp eP) :
    Module.Projective R (Middle dQ dP f) :=
  projective_of_exact (inclusion dQ dP f) (projection dQ dP f)
    (inclusion_injective dQ dP f eP f₁ hex hc) (projection_surjective dQ dP f)
    (exact dQ dP f)

end ConeCokernel
end ArExplicit

end

end OAI
