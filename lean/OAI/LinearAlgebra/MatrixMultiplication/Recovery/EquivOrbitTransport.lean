import OAI.LinearAlgebra.MatrixMultiplication.Recovery.OrbitCounting
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.EquivOrbitTransport

variable {G X Y : Type*} [Group G] [MulAction G Y]

@[instance_reducible] def action (e : X ≃ Y) : MulAction G X where
  smul g x := e.symm (g • e x)
  one_smul x := by
    change e.symm ((1 : G) • e x) = x
    simp
  mul_smul g h x := by
    change e.symm ((g * h) • e x) = e.symm (g • e (e.symm (h • e x)))
    simp [mul_smul]

@[simp] theorem equiv_smul (e : X ≃ Y) (g : G) (x : X) :
    letI : MulAction G X := action e
    e (g • x) = g • e x := by
  exact e.apply_symm_apply _

section Finite

variable [Fintype G] [DecidableEq X] [DecidableEq Y]

theorem orbitSet_map (e : X ≃ Y) (x : X) :
    letI : MulAction G X := action e
    (OrbitCounting.orbitSet (G := G) x).map e.toEmbedding =
      OrbitCounting.orbitSet (G := G) (e x) := by
  let : MulAction G X := action e
  change (Finset.univ.image fun g : G => e.symm (g • e x)).map e.toEmbedding = _
  simp only [Finset.map_eq_image, Finset.image_image, Function.comp_def,
    Equiv.toEmbedding_apply, Equiv.apply_symm_apply, OrbitCounting.orbitSet]

theorem orbitSet_card (e : X ≃ Y) (x : X) :
    letI : MulAction G X := action e
    (OrbitCounting.orbitSet (G := G) x).card =
      (OrbitCounting.orbitSet (G := G) (e x)).card := by
  let : MulAction G X := action e
  simpa only [Finset.card_map] using congrArg Finset.card (orbitSet_map e x)

theorem rejected_card (e : X ≃ Y) (bad : X → Prop) [DecidablePred bad] (x : X) :
    letI : MulAction G X := action e
    ((OrbitCounting.orbitSet (G := G) x).filter bad).card =
      ((OrbitCounting.orbitSet (G := G) (e x)).filter (bad ∘ e.symm)).card := by
  let : MulAction G X := action e
  calc
    ((OrbitCounting.orbitSet (G := G) x).filter bad).card =
        (((OrbitCounting.orbitSet (G := G) x).filter bad).map e.toEmbedding).card :=
      (Finset.card_map _).symm
    _ = _ := by rw [Finset.map_filter, orbitSet_map]

theorem rejected_fraction (e : X ≃ Y) (bad : X → Prop) [DecidablePred bad] (x : X) :
    letI : MulAction G X := action e
    (((OrbitCounting.orbitSet (G := G) x).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card =
      (((OrbitCounting.orbitSet (G := G) (e x)).filter (bad ∘ e.symm)).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) (e x)).card := by
  let : MulAction G X := action e
  rw [rejected_card e bad x, orbitSet_card e x]

end Finite

theorem coefficients_preserved
    {K RX RY RZ CX CY CZ : Type*} [CommSemiring K]
    [MulAction G CX] [MulAction G CY] [MulAction G CZ]
    (ex : RX ≃ CX) (ey : RY ≃ CY) (ez : RZ ≃ CZ)
    (raw : Tensor K RX RY RZ) (canonical : Tensor K CX CY CZ)
    (hcoords : ∀ x y z, raw x y z = canonical (ex x) (ey y) (ez z))
    (hcanonical : ∀ (g : G) x y z,
      canonical (g • x) (g • y) (g • z) = canonical x y z) :
    letI : MulAction G RX := action ex
    letI : MulAction G RY := action ey
    letI : MulAction G RZ := action ez
    ∀ (g : G) x y z, raw (g • x) (g • y) (g • z) = raw x y z := by
  let : MulAction G RX := action ex
  let : MulAction G RY := action ey
  let : MulAction G RZ := action ez
  intro g x y z
  rw [hcoords, hcoords]
  change canonical (ex (ex.symm (g • ex x))) (ey (ey.symm (g • ey y)))
    (ez (ez.symm (g • ez z))) = _
  simpa only [Equiv.apply_symm_apply] using hcanonical g (ex x) (ey y) (ez z)

end MatrixMultiplication.EquivOrbitTransport

end OAI
