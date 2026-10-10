import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Detector.Row
import OAI.NumberTheory.DirichletL.Detector.Compensation

namespace OAI

noncomputable section

open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbeCompleted ProbeRow

local notation "O" => ActualEisensteinCubic.O

structure CalibrationData where
  excluded : Finset (Ideal O)
  generator : O
  generator_ne_zero : generator ≠ 0
  residue : MulChar (O ⧸ Ideal.span {generator}) ℂ

def elementNorm (a : O) : ℝ := Ideal.absNorm (Ideal.span {a})

def CalibrationData.residueMonoid (C : CalibrationData) : O →* ℂ :=
  C.residue.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {C.generator})).toMonoidHom

def CalibrationData.Xi (C : CalibrationData) : O →* ℂ :=
  C.residueMonoid * (idealRowHom C.generator).toMonoidHom.comp principalIdealHom.toMonoidHom

def CalibrationData.tau (C : CalibrationData) : ℂ :=
  (∑' d : O ⧸ Ideal.span {C.generator}, C.residue d *
    quotientTrace C.generator C.generator_ne_zero d) /
      (Real.sqrt (elementNorm C.generator) : ℂ)

def sexticGauss (s : O) (hs : s ≠ 0) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {s},
    idealRowHom (GaussianShiftedPartition.representative s d) (Ideal.span {s}) *
      quotientTrace s hs (Ideal.Quotient.mk _ h * d)

theorem sexticGauss_coefficient_mk (s : O) (a : O) :
    idealRowHom (GaussianShiftedPartition.representative s
      (Ideal.Quotient.mk (Ideal.span {s}) a)) (Ideal.span {s}) =
      idealRowHom a (Ideal.span {s}) := by
  apply idealRowHom_congr_mod
  apply Ideal.Quotient.eq.mp
  exact GaussianShiftedPartition.representative_spec _ _

def verticalIntegral (σ : ℝ) (F : ℂ → ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, F ((σ : ℂ) + y * Complex.I)

def markedPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p ∈ C.excluded, ¬p ∣ s.val then
      let a := primaryGenerator s.val
      let ha := supported_primaryGenerator_ne_zero s.val s.property
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s / Y) * idealRowHom C.generator s.val /
        (C.tau * C.residueMonoid a * (Real.sqrt (elementNorm C.generator * q_s * X) : ℂ)) *
      ∑' m : O,
        C.residueMonoid m * (Real.sqrt q_s : ℂ)⁻¹ * sexticGauss a ha (-m) *
          W₀ (elementNorm m / (elementNorm C.generator * q_s * X)) *
          verticalIntegral 4 (fun t => (Z : ℂ) ^ t * Complex.exp (t ^ 2) *
            spectralRow C.excluded D (rowCoefficient η C.Xi a has m) t)
    else 0

def physicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  markedPhysicalProbe η C 1 W₀ W₁ X Y Z

def slotProduct {K : ℕ} (p : Fin K → O) (J : Finset (Fin K)) : O := ∏ i ∈ J, p i

def compensatedTuple {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin K → O) (X Y Z : ℝ) : ℂ :=
  ProbeCompensation.tupleOperation p elementNorm (HeckeFamily.elementCoeff η)
    (fun a => markedPhysicalProbe η C (Ideal.span {a}) W₀ W₁) X Y Z

@[simp] theorem elementNorm_one : elementNorm (1 : O) = 1 := by
  simp [elementNorm]

attribute [local irreducible] markedPhysicalProbe

theorem compensatedTuple_zero (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin 0 → O) (X Y Z : ℝ) :
    compensatedTuple η C W₀ W₁ p X Y Z = physicalProbe η C W₀ W₁ X Y Z := by
  unfold compensatedTuple
  rw [ProbeCompensation.tupleOperation_zero p elementNorm (HeckeFamily.elementCoeff η)
    elementNorm_one (HeckeFamily.elementCoeff_one η)]
  change markedPhysicalProbe η C (Ideal.span {(1 : O)}) W₀ W₁ X Y Z =
    markedPhysicalProbe η C 1 W₀ W₁ X Y Z
  rw [Ideal.span_singleton_one, Ideal.one_eq_top]

theorem compensatedTuple_one (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin 1 → O) (X Y Z : ℝ) :
    compensatedTuple η C W₀ W₁ p X Y Z =
      star (HeckeFamily.elementCoeff η (p 0)) *
        markedPhysicalProbe η C (Ideal.span {p 0}) W₀ W₁ X Y (Z * elementNorm (p 0)) -
      (elementNorm (p 0) ^ (-(3 / 2 : ℝ)) : ℝ) *
        physicalProbe η C W₀ W₁ (X / elementNorm (p 0)) (Y / elementNorm (p 0)) Z := by
  unfold compensatedTuple
  rw [ProbeCompensation.tupleOperation_one p elementNorm (HeckeFamily.elementCoeff η)
    elementNorm_one (HeckeFamily.elementCoeff_one η)]
  change _ = _ - _ * markedPhysicalProbe η C 1 W₀ W₁ _ _ Z
  rw [Ideal.span_singleton_one, Ideal.one_eq_top]

def compensatedPhysicalProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (slotPrimes : Fin K → Finset O)
    (slotWindow : Fin K → ℝ → ℂ) (slotScale : Fin K → ℝ) (X Y Z : ℝ) : ℂ :=
  ∑ p : ((i : Fin K) → {a : O // a ∈ slotPrimes i}),
    (∏ i : Fin K, slotWindow i (elementNorm (p i).val / slotScale i)) *
      compensatedTuple η C W₀ W₁ (fun i => (p i).val) X Y Z

end SevenEighths.ProbePhysical
end

end OAI
