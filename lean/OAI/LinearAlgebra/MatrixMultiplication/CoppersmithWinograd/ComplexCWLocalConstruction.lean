import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialLocalConstruction
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCWOriginalWords

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation.CWLocalConstruction

open Tensor OrientationRates CWOriginalWords PolynomialLocalConstruction

abbrev Site (m : ℕ) := Orientation × Fin m

@[simp] theorem site_card (m : ℕ) : Fintype.card (Site m) = 6 * m := by
  simp only [Site, Fintype.card_prod, orientation_card, Fintype.card_fin]

def siteEquiv (m : ℕ) : Fin (6 * m) ≃ Site m :=
  (Fintype.equivFinOfCardEq (site_card m)).symm

def sourceApproximation (m : ℕ) :
    PolynomialApproximation (siteTensor (Site := Site m))
      (3 ^ (6 * m)) (2 * (6 * m)) (6 * (6 * m)) := by
  have W := (CoppersmithWinograd.approximation.power (6 * m)).pullback
    (fun x : Site m → Fin 3 => fun i => x (siteEquiv m i))
    (fun y : Site m → Fin 3 => fun i => y (siteEquiv m i))
    (fun z : Site m → Fin 3 => fun i => z (siteEquiv m i))
  have hsource : Tensor.pullback
      (fun x : Site m → Fin 3 => fun i => x (siteEquiv m i))
      (fun y : Site m → Fin 3 => fun i => y (siteEquiv m i))
      (fun z : Site m → Fin 3 => fun i => z (siteEquiv m i))
      (Tensor.power CoppersmithWinograd.tensor (6 * m)) =
        siteTensor (Site := Site m) := by
    funext x y z
    exact (siteTensor_eq_power (siteEquiv m) x y z).symm
  rw [hsource] at W
  exact W

variable {AX AY AZ Label : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ] [Fintype Label] [DecidableEq Label]
variable {m a b c : ℕ}

abbrev CWPrimitive (m a b c : ℕ) :=
  Primitive (Site m → Fin 3) (Site m → Fin 3) (Site m → Fin 3)
    AX AY AZ Label OriginalComponent m a b c

variable (P : CWPrimitive (AX := AX) (AY := AY) (AZ := AZ) (Label := Label) m a b c)

def word (label : Label) : Site m → OriginalComponent :=
  fun site => P.word label site.1 site.2

structure SourceCompatible (physical : Site m → Orientation) : Prop where
  support_contains : ∀ x y z,
    siteTensor x y z ≠ 0 → P.support x y z
  grade_decodes : ∀ x y z, siteTensor x y z ≠ 0 →
    originalWords (permuteWord physical
      (fun site => P.gradeOf x y z site.1 site.2)) = (x, y, z)
  designated_coordinates : ∀ label,
    (P.designatedX label, P.designatedY label, P.designatedZ label) =
      originalWords (permuteWord physical (word P label))

namespace SourceCompatible

variable {P} {physical : Site m → Orientation}
variable (h : SourceCompatible P physical)

include h

theorem inputSupported : P.InputSupported (siteTensor (Site := Site m)) := by
  intro x y z hs
  by_contra hn
  exact hs (h.support_contains x y z hn)

theorem designatedCoefficients :
    P.DesignatedCoefficients (siteTensor (Site := Site m)) := by
  intro label
  have hc := congrArg (fun xyz => siteTensor xyz.1 xyz.2.1 xyz.2.2)
    (h.designated_coordinates label)
  exact hc.trans (siteTensor_oriented_originalWords physical (word P label))

theorem grade_eq_word_iff (x y z : Site m → Fin 3)
    (nonzero : siteTensor x y z ≠ 0) (label : Label) :
    P.gradeOf x y z = P.word label ↔
      (x, y, z) = (P.designatedX label, P.designatedY label, P.designatedZ label) := by
  constructor
  · intro hgrade
    calc
      (x, y, z) = originalWords (permuteWord physical
          (fun site => P.gradeOf x y z site.1 site.2)) :=
        (h.grade_decodes x y z nonzero).symm
      _ = originalWords (permuteWord physical (word P label)) := by rw [hgrade]; rfl
      _ = (P.designatedX label, P.designatedY label, P.designatedZ label) :=
        (h.designated_coordinates label).symm
  · intro hcoordinates
    calc
      P.gradeOf x y z = P.gradeOf (P.designatedX label) (P.designatedY label)
          (P.designatedZ label) :=
        congrArg (fun xyz => P.gradeOf xyz.1 xyz.2.1 xyz.2.2) hcoordinates
      _ = P.word label := P.designated_word label

def terminalApproximation :
    PolynomialApproximation
      (Tensor.directSum (fun _ : Label =>
        matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c)))
      (3 ^ (6 * m) * P.rankBound)
      ((2 * (6 * m)) * (P.order + 1) + P.order)
      ((6 * (6 * m)) * (P.order + 1) +
        P.leftDegree + P.middleDegree + P.rightDegree) :=
  P.terminalApproximation (sourceApproximation m)
    h.inputSupported h.designatedCoefficients

end SourceCompatible

structure Admissible (physical : Site m → Orientation) : Prop
    extends SourceCompatible P physical where
  pairing_budget : a * b * c ≤ P.rankBound

namespace Admissible

variable {P} {physical : Site m → Orientation}

theorem rankBound_pos (h : Admissible P physical) : 0 < P.rankBound :=
  lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos P.leftDim_pos P.middleDim_pos)
    P.rightDim_pos) h.pairing_budget

end Admissible
end MatrixMultiplication.Foundation.CWLocalConstruction

end

end OAI
