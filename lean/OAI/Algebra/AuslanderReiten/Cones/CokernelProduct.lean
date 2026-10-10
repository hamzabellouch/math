import OAI.Algebra.AuslanderReiten.Cones.CokernelLinearCongr

namespace OAI

noncomputable section
namespace ArExplicit

variable {R M N P Q : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

def cokernelProductMap (f : M →ₗ[R] N) (g : P →ₗ[R] Q) :
    (N × Q) ⧸ LinearMap.range (f.prodMap g) →ₗ[R]
      (N ⧸ LinearMap.range f) × (Q ⧸ LinearMap.range g) :=
  (LinearMap.range (f.prodMap g)).liftQ
    (((LinearMap.range f).mkQ).prodMap ((LinearMap.range g).mkQ)) (by
      rintro x ⟨⟨m, p⟩, rfl⟩
      change (Submodule.Quotient.mk (f m), Submodule.Quotient.mk (g p)) = (0, 0)
      exact Prod.ext ((Submodule.Quotient.mk_eq_zero _).mpr ⟨m, rfl⟩)
        ((Submodule.Quotient.mk_eq_zero _).mpr ⟨p, rfl⟩))

@[simp]
theorem cokernelProductMap_mk (f : M →ₗ[R] N) (g : P →ₗ[R] Q) (n : N) (q : Q) :
    cokernelProductMap f g (Submodule.Quotient.mk (n, q)) =
      (Submodule.Quotient.mk n, Submodule.Quotient.mk q) := rfl

theorem cokernelProductMap_bijective (f : M →ₗ[R] N) (g : P →ₗ[R] Q) :
    Function.Bijective (cokernelProductMap f g) := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨⟨n, q⟩, rfl⟩ := (LinearMap.range (f.prodMap g)).mkQ_surjective x
    obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_eq_zero _).mp (congrArg Prod.fst hx)
    obtain ⟨p, hp⟩ := (Submodule.Quotient.mk_eq_zero _).mp (congrArg Prod.snd hx)
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨(m, p), Prod.ext hm hp⟩
  · rintro ⟨n, q⟩
    obtain ⟨n, rfl⟩ := (LinearMap.range f).mkQ_surjective n
    obtain ⟨q, rfl⟩ := (LinearMap.range g).mkQ_surjective q
    exact ⟨Submodule.Quotient.mk (n, q), rfl⟩

def cokernelProductEquiv (f : M →ₗ[R] N) (g : P →ₗ[R] Q) :
    ((N × Q) ⧸ LinearMap.range (f.prodMap g)) ≃ₗ[R]
      (N ⧸ LinearMap.range f) × (Q ⧸ LinearMap.range g) :=
  LinearEquiv.ofBijective (cokernelProductMap f g) (cokernelProductMap_bijective f g)

@[simp]
theorem cokernelProductEquiv_mk (f : M →ₗ[R] N) (g : P →ₗ[R] Q) (n : N) (q : Q) :
    cokernelProductEquiv f g (Submodule.Quotient.mk (n, q)) =
      (Submodule.Quotient.mk n, Submodule.Quotient.mk q) := rfl

end ArExplicit

end

end OAI
