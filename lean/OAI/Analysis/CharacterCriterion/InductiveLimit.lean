import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.CentralSequences

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


open scoped TensorProduct CStarAlgebra

namespace KirchbergRordam
namespace StarCompletion

open UniformSpace
variable (R : Type*) [SeminormedRing R] [StarRing R] [NormedStarGroup R]


@[simp]
lemma star_coe (x : R) : star (x : Completion R) = (star x : R) :=
  Completion.map_coe star_isometry.uniformContinuous x


instance completionNormedStarGroup : NormedStarGroup (Completion R) where
  norm_star_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simp only [star_coe, Completion.norm_coe, norm_star, le_refl]

variable [NormedAlgebra ℂ R] [StarModule ℂ R]


end StarCompletion

end KirchbergRordam


namespace KirchbergRordam.CStarInductiveLimit
section
universe u


attribute [instance] System.cstar


@[simp] lemma rawOf_map (S : System) (i j : ℕ) (h : i ≤ j) (x : S.obj i) :
    rawOf S j (S.map i j h x) = rawOf S i x := DirectLimit.mk_apply _ _ _ _


@[simp] lemma normLift_mk (S : System) (n : ℕ) (x : S.obj n) :
    normLift S (rawOf S n x) = ‖x‖ := rfl


@[simp] theorem norm_rawOf (S : System) (n : ℕ) (x : S.obj n) :
    ‖rawOf S n x‖ = ‖x‖ := rfl


def rawInclusion (S : System) : Raw S →⋆ₐ[ℂ] Algebra S where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl
  map_star' _ := (StarCompletion.star_coe _ _).symm

def of (S : System) (n : ℕ) : S.obj n →⋆ₐ[ℂ] Algebra S :=
  (rawInclusion S).comp (rawOf S n)

@[simp] theorem of_map (S : System) (i j : ℕ) (h : i ≤ j) (x : S.obj i) :
    of S j (S.map i j h x) = of S i x := by
  change rawInclusion S (rawOf S j (S.map i j h x)) = _
  rw [rawOf_map]
  rfl

@[simp] theorem norm_of (S : System) (n : ℕ) (x : S.obj n) : ‖of S n x‖ = ‖x‖ :=
  (UniformSpace.Completion.norm_coe _).trans (norm_rawOf S n x)

theorem of_isometry (S : System) (n : ℕ) : Isometry (of S n) := by
  apply AddMonoidHomClass.isometry_of_norm
  exact norm_of S n

instance (S : System) [Nontrivial (S.obj 0)] : Nontrivial (Algebra S) :=
  (of_isometry S 0).injective.nontrivial


variable {C : Type*} [CStarAlgebra C]

def rawLift (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) :
    Raw S →⋆ₐ[ℂ] C where
  __ := DirectLimit.Algebra.lift S.obj S.map C (fun n => (f n).toAlgHom) hf
  map_star' x := by
    refine DirectLimit.induction S.map ?_ x
    intro n x
    exact map_star (f n) x

@[simp] theorem rawLift_of (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x)
    (n : ℕ) (x : S.obj n) : rawLift S f hf (rawOf S n x) = f n x := rfl

theorem norm_rawLift_le (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x)
    (x : Raw S) : ‖rawLift S f hf x‖ ≤ ‖x‖ := by
  refine DirectLimit.induction S.map ?_ x
  intro n x
  exact NonUnitalStarAlgHom.norm_apply_le (f n) x

theorem continuous_rawLift (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) :
    Continuous (rawLift S f hf) := by
  exact ((rawLift S f hf).toLinearMap.mkContinuous 1
    (fun x => by
      change ‖rawLift S f hf x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using norm_rawLift_le S f hf x)).continuous


def lift (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) :
    Algebra S →⋆ₐ[ℂ] C where
  __ := UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
    (continuous_rawLift S f hf)
  commutes' z := by
    change UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
      (continuous_rawLift S f hf) (algebraMap ℂ (Raw S) z) = algebraMap ℂ C z
    rw [UniformSpace.Completion.extensionHom_coe]
    exact (rawLift S f hf).commutes z
  map_star' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_extension.comp continuous_star)
        (continuous_star.comp UniformSpace.Completion.continuous_extension)
    | ih x =>
      change UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
        (continuous_rawLift S f hf) (star (x : Algebra S)) =
        star (UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
          (continuous_rawLift S f hf) (x : Algebra S))
      simp only [StarCompletion.star_coe, UniformSpace.Completion.extensionHom_coe]
      exact map_star (rawLift S f hf) x

@[simp] theorem lift_rawInclusion (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) (x : Raw S) :
    lift S f hf (rawInclusion S x) = rawLift S f hf x :=
  UniformSpace.Completion.extensionHom_coe (rawLift S f hf).toRingHom
    (continuous_rawLift S f hf) x

@[simp] theorem lift_of (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x)
    (n : ℕ) (x : S.obj n) : lift S f hf (of S n x) = f n x := by
  change lift S f hf (rawInclusion S (rawOf S n x)) = _
  rw [lift_rawInclusion, rawLift_of]


theorem induction_on (S : System) {P : Algebra S → Prop} (x : Algebra S)
    (hclosed : IsClosed {x | P x}) (hof : ∀ n x, P (of S n x)) : P x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih x =>
    refine DirectLimit.induction S.map ?_ x
    exact hof


theorem hom_ext (S : System) (f g : Algebra S →⋆ₐ[ℂ] C)
    (h : ∀ n x, f (of S n x) = g (of S n x)) : f = g := by
  ext x
  exact induction_on S x (isClosed_eq (map_continuous f) (map_continuous g)) h

theorem denseRange_of (S : System) :
    DenseRange (fun p : Σ n, S.obj n => of S p.1 p.2) := by
  intro x
  exact induction_on S x isClosed_closure
    (fun n x => subset_closure ⟨⟨n,x⟩,rfl⟩)


instance (S : System) [∀ n, TopologicalSpace.SeparableSpace (S.obj n)] :
    TopologicalSpace.SeparableSpace (Algebra S) :=
  (denseRange_of S).separableSpace (continuous_sigma fun n => map_continuous (of S n))

end

universe u


attribute [instance] Chain.cstar


@[simp] lemma Chain.map_self (S : Chain) (i : ℕ) :
    S.map i i le_rfl = StarAlgHom.id ℂ _ := by simp [Chain.map, Nat.leRecOn_self]

@[simp] lemma Chain.map_succ (S : Chain) (i j : ℕ) (h : i ≤ j) :
    S.map i (j+1) (h.trans (Nat.le_succ j)) = (S.step j).comp (S.map i j h) := by
  exact Nat.leRecOn_succ (C := fun n => S.obj i →⋆ₐ[ℂ] S.obj n)
    (next := fun {n} φ => (S.step n).comp φ) h (StarAlgHom.id ℂ (S.obj i))

lemma Chain.map_map (S : Chain) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k)
    (x : S.obj i) : S.map j k hjk (S.map i j hij x) = S.map i k (hij.trans hjk) x := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    rw [S.map_succ j k hjk, S.map_succ i k (hij.trans hjk)]
    exact congrArg (S.step k) ih

lemma Chain.norm_map (S : Chain) (i j : ℕ) (h : i ≤ j) (x : S.obj i) :
    ‖S.map i j h x‖ = ‖x‖ := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j h ih =>
    rw [S.map_succ i j h]
    exact (S.norm_step j (S.map i j h x)).trans ih


end KirchbergRordam.CStarInductiveLimit


end

end OAI
