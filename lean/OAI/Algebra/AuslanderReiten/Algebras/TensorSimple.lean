import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorRegular
import OAI.Algebra.AuslanderReiten.Algebras.TSocle
import OAI.Algebra.AuslanderReiten.Algebras.TensorFrobenius
import OAI.Algebra.AuslanderReiten.Algebras.SymmetricSocle

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

abbrev Simple := ExternalTensor.moduleObject k R R S S

def simpleCoordinate : S ⊗[k] S →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp
    (TensorProduct.map (Resolution.simpleCoordinate q) (Resolution.simpleCoordinate q))

@[simp] theorem simpleCoordinate_tmul (s t : S) :
    simpleCoordinate q (s ⊗ₜ[k] t) =
      Resolution.simpleCoordinate q s * Resolution.simpleCoordinate q t := rfl

def simpleCoordinateEquiv (hq1 : 1 + q ≠ 0) : Simple q ≃ₗ[k] k :=
  (TensorProduct.congr (Resolution.simpleCoordinateEquiv q hq1)
    (Resolution.simpleCoordinateEquiv q hq1)).trans (TensorProduct.lid k k)

theorem simpleCoordinate_injective (hq1 : 1 + q ≠ 0) :
    Function.Injective (simpleCoordinate q) := (simpleCoordinateEquiv q hq1).injective

def simpleGenerator : Simple q := CocycleData.simpleGenerator q ⊗ₜ[k] CocycleData.simpleGenerator q

@[simp] theorem simpleGenerator_coordinate : simpleCoordinate q (simpleGenerator q) = 1 := by
  simp [simpleGenerator]

def simpleCharacter : A k q →ₐ[k] k :=
  Algebra.TensorProduct.lift (T.simpleCharacter q) (T.simpleCharacter q)
    (fun _ _ => Commute.all _ _)

@[simp] theorem simpleCharacter_tmul (a b : R) :
    simpleCharacter q (a ⊗ₜ[k] b) = T.simpleCharacter q a * T.simpleCharacter q b := rfl

theorem simpleCoordinate_smul (a : A k q) (x : Simple q) :
    simpleCoordinate q (a • x) = simpleCharacter q a * simpleCoordinate q x := by
  let w : S ⊗[k] S := x
  change simpleCoordinate q (ExternalTensor.representation k R R S S a w) =
    simpleCharacter q a * simpleCoordinate q w
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_mul]
  | tmul a b =>
    induction w using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, mul_add]
    | tmul s t =>
      change Resolution.simpleCoordinate q (a • s) * Resolution.simpleCoordinate q (b • t) =
        (T.simpleCharacter q a * T.simpleCharacter q b) *
          (Resolution.simpleCoordinate q s * Resolution.simpleCoordinate q t)
      rw [Resolution.t_simple_character, Resolution.t_simple_character]
      change (a.base.coeff .f * _) * (b.base.coeff .f * _) =
        (a.base.coeff .f * b.base.coeff .f) * (_ * _)
      ring

def augmentationIdeal : Ideal (A k q) := RingHom.ker (simpleCharacter q)

instance : (augmentationIdeal q).IsTwoSided := inferInstanceAs
  (RingHom.ker (simpleCharacter q)).IsTwoSided

theorem augmentationIdeal_annihilates (hq1 : 1 + q ≠ 0)
    (a : A k q) (ha : a ∈ augmentationIdeal q) (x : Simple q) : a • x = 0 := by
  apply simpleCoordinate_injective q hq1
  rw [simpleCoordinate_smul, show simpleCharacter q a = 0 from ha, zero_mul]
  change 0 = simpleCoordinate q (0 : S ⊗[k] S)
  exact (map_zero _).symm

def socleMap : Simple q →ₗ[A k q] A k q :=
  (ExternalTensor.regularEquiv k R R).toLinearMap.comp
    (ExternalTensor.map k R R (T.socleMap q) (T.socleMap q))

@[simp] theorem socleMap_tmul (s t : S) :
    socleMap q (s ⊗ₜ[k] t) = T.socleMap q s ⊗ₜ[k] T.socleMap q t := rfl

@[simp] theorem socleMap_generator :
    socleMap q (simpleGenerator q) = T.upper q .f ⊗ₜ[k] T.upper q .f := by
  simp [simpleGenerator]

theorem socleMap_mem (x : Simple q) : socleMap q x ∈ augmentationIdeal q := by
  let w : S ⊗[k] S := x
  let F : S ⊗[k] S →ₗ[k] A k q :=
    TensorProduct.map ((T.socleMap q).restrictScalars k) ((T.socleMap q).restrictScalars k)
  change simpleCharacter q (F w) = 0
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul s t =>
    change simpleCharacter q (T.socleMap q s ⊗ₜ[k] T.socleMap q t) = 0
    rw [simpleCharacter_tmul]
    have hz (u : S) : T.simpleCharacter q (T.socleMap q u) = 0 := by
      change ((Resolution.simpleCoordinate q u) • T.upper q .f).base.coeff .f = 0
      simp [T.upper, TrivialExtension.inr]
    rw [hz, zero_mul]

def beta : Simple q →ₗ[A k q] augmentationIdeal q :=
  (socleMap q).codRestrict (augmentationIdeal q) (socleMap_mem q)

end ArExplicit.A

end

end OAI
