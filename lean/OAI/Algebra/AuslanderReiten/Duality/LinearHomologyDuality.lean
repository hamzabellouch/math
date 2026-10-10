import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

namespace ArExplicit.LinearHomology

universe u

variable {k : Type u} [Field k]
variable {U V W : Type u}
variable [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

def cycleMap (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) : U →ₗ[k] LinearMap.ker g :=
  f.codRestrict (LinearMap.ker g) (fun x => DFunLike.congr_fun h x)

def boundaries (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) :
    Submodule k (LinearMap.ker g) := LinearMap.range (cycleMap f g h)

abbrev Homology (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) :=
  LinearMap.ker g ⧸ boundaries f g h

theorem dual_comp (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) :
    f.dualMap.comp g.dualMap = 0 := by
  ext φ x
  change φ (g (f x)) = 0
  rw [show g (f x) = 0 from DFunLike.congr_fun h x, map_zero]

def dualCyclesToDualHomology (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) :
    LinearMap.ker f.dualMap →ₗ[k] Module.Dual k (Homology f g h) where
  toFun φ := (boundaries f g h).liftQ (φ.val.comp (LinearMap.ker g).subtype) (by
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun φ.property x)
  map_add' φ ψ := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    rfl
  map_smul' c φ := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    rfl

@[simp]
theorem dualCyclesToDualHomology_mk (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0)
    (φ : LinearMap.ker f.dualMap) (x : LinearMap.ker g) :
    dualCyclesToDualHomology f g h φ ((boundaries f g h).mkQ x) = φ.val x.val := rfl

theorem dualCyclesToDualHomology_surjective (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (h : g.comp f = 0) : Function.Surjective (dualCyclesToDualHomology f g h) := by
  intro l
  obtain ⟨φ, hφ⟩ := (l.comp (boundaries f g h).mkQ).exists_extend
  have hp : φ ∈ LinearMap.ker f.dualMap := by
    apply LinearMap.ext
    intro x
    have hx := DFunLike.congr_fun hφ (cycleMap f g h x)
    change φ (f x) = 0
    change φ (f x) = l ((boundaries f g h).mkQ (cycleMap f g h x)) at hx
    rw [show (boundaries f g h).mkQ (cycleMap f g h x) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero] at hx
    exact hx
  refine ⟨⟨φ, hp⟩, ?_⟩
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
  exact DFunLike.congr_fun hφ x

theorem dualCyclesToDualHomology_kernel (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (h : g.comp f = 0) :
    LinearMap.ker (dualCyclesToDualHomology f g h) =
      boundaries g.dualMap f.dualMap (dual_comp f g h) := by
  ext φ
  constructor
  · intro hφ
    have ha : φ.val ∈ (LinearMap.ker g).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      exact DFunLike.congr_fun hφ ((boundaries f g h).mkQ ⟨x, hx⟩)
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at ha
    obtain ⟨ψ, hψ⟩ := ha
    exact ⟨ψ, Subtype.ext hψ⟩
  · rintro ⟨ψ, rfl⟩
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    change ψ (g x.val) = 0
    rw [x.property, map_zero]

noncomputable def dualHomologyEquiv (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) :
    Module.Dual k (Homology f g h) ≃ₗ[k]
      Homology g.dualMap f.dualMap (dual_comp f g h) :=
  ((Submodule.quotEquivOfEq _ _ (dualCyclesToDualHomology_kernel f g h).symm).trans
    ((dualCyclesToDualHomology f g h).quotKerEquivOfSurjective
      (dualCyclesToDualHomology_surjective f g h))).symm

@[simp]
theorem dualHomologyEquiv_symm_mk (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0)
    (φ : LinearMap.ker f.dualMap) :
    (dualHomologyEquiv f g h).symm
      (Submodule.Quotient.mk φ) =
      dualCyclesToDualHomology f g h φ := by
  simp only [dualHomologyEquiv, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

end ArExplicit.LinearHomology

end OAI
