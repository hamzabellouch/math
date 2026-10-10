import OAI.Algebra.AuslanderReiten.Evaluation.TensorBeta
import OAI.Algebra.AuslanderReiten.Stable.StableHomEquiv

namespace OAI

noncomputable section
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] (q : k) (hq1 : 1 + q ≠ 0)

include hq1 in

theorem simple_not_projective : ¬ Module.Projective (A k q) (Simple q) := by
  intro hp
  let := hp
  let : Module.Finite (A k q) (Simple q) := Module.Finite.of_restrictScalars_finite k (A k q) _
  exact beta_stable_ne_zero q hq1 (StableHom.eq_zero_of_projective_source _)

include hq1 in
theorem simple_scalar_generator (x : Simple q) :
    x = simpleCoordinate q x • simpleGenerator q := by
  apply simpleCoordinate_injective q hq1
  erw [(simpleCoordinate q).map_smul, simpleGenerator_coordinate]
  exact (mul_one _).symm

def endScalar : (Simple q →ₗ[A k q] Simple q) →ₗ[k] k where
  toFun f := simpleCoordinate q (f (simpleGenerator q))
  map_add' left right :=
    (simpleCoordinate q).map_add (left (simpleGenerator q)) (right (simpleGenerator q))
  map_smul' scalar endomorphism :=
    (simpleCoordinate q).map_smul scalar (endomorphism (simpleGenerator q))

include hq1 in
theorem end_eq_scalar_id (f : Simple q →ₗ[A k q] Simple q) :
    f = endScalar q f • LinearMap.id := by
  apply LinearMap.ext
  intro x
  change f x = endScalar q f • x
  calc
    f x = f (simpleCoordinate q x • simpleGenerator q) := congrArg f (simple_scalar_generator q hq1 x)
    _ = simpleCoordinate q x • f (simpleGenerator q) := (f.restrictScalars k).map_smul _ _
    _ = simpleCoordinate q x • (endScalar q f • simpleGenerator q) := by
      exact congrArg (fun z => simpleCoordinate q x • z)
        (simple_scalar_generator q hq1 (f (simpleGenerator q)))
    _ = endScalar q f • (simpleCoordinate q x • simpleGenerator q) := smul_comm _ _ _
    _ = endScalar q f • x := congrArg (fun z => endScalar q f • z) (simple_scalar_generator q hq1 x).symm

def simpleEndEquiv : (Simple q →ₗ[A k q] Simple q) ≃ₗ[k] k where
  __ := endScalar q
  invFun c := c • LinearMap.id
  left_inv f := (end_eq_scalar_id q hq1 f).symm
  right_inv c := by
    change simpleCoordinate q (c • simpleGenerator q) = c
    erw [(simpleCoordinate q).map_smul, simpleGenerator_coordinate]
    exact mul_one _

include hq1 in
theorem stable_identity_ne_zero :
    StableHom.classOf (A k q) (Simple q) (Simple q) LinearMap.id ≠ 0 := by
  let : Module.Finite (A k q) (Simple q) := Module.Finite.of_restrictScalars_finite k (A k q) _
  intro h
  exact simple_not_projective q hq1 (StableHom.identity_eq_zero_iff.mp h)

include hq1 in

theorem simpleEnd_classOf_injective : Function.Injective
    (StableHom.classOfLinear k : (Simple q →ₗ[A k q] Simple q) →ₗ[k]
      StableHom (A k q) (Simple q) (Simple q)) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro f hf
  have hz : StableHom.classOf (A k q) (Simple q) (Simple q) f = 0 := hf
  rw [end_eq_scalar_id q hq1 f, StableHom.classOf_smul] at hz
  have hc : endScalar q f = 0 := (smul_eq_zero.mp hz).resolve_right (stable_identity_ne_zero q hq1)
  rw [end_eq_scalar_id q hq1 f, hc, zero_smul]
  exact Submodule.zero_mem _

def stableEndEquiv : StableHom (A k q) (Simple q) (Simple q) ≃ₗ[k] k :=
  (LinearEquiv.ofBijective (StableHom.classOfLinear k)
    ⟨simpleEnd_classOf_injective q hq1, StableHom.classOf_surjective⟩).symm.trans
      (simpleEndEquiv q hq1)

@[simp]
theorem stableEndEquiv_classOf (f : Simple q →ₗ[A k q] Simple q) :
    stableEndEquiv q hq1 (StableHom.classOf (A k q) _ _ f) = endScalar q f := by
  change simpleEndEquiv q hq1 ((LinearEquiv.ofBijective (StableHom.classOfLinear k) _).symm
    ((StableHom.classOfLinear k) f)) = _
  erw [LinearEquiv.symm_apply_apply]
  rfl

@[simp]
theorem stableEndEquiv_identity : stableEndEquiv q hq1 StableHom.identity = 1 := by
  change stableEndEquiv q hq1 (StableHom.classOf _ _ _ LinearMap.id) = 1
  rw [stableEndEquiv_classOf]
  exact simpleGenerator_coordinate q

end ArExplicit.A

end

end OAI
