import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalSourceSubtraction

namespace OAI

/-! Linearity of the actual physical source under outgoing column combinations. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralPhysicalJordanSource (U : E₄) : E₄ :=
  ((0,-Complex.I*U.1.1),(0,Complex.I*U.2.1))

theorem spectralPhysicalJordanSource_add (U V : E₄) :
    spectralPhysicalJordanSource (U+V)=spectralPhysicalJordanSource U+spectralPhysicalJordanSource V := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralPhysicalJordanSource,Prod.fst_add,Prod.snd_add,mul_add,zero_add]

theorem spectralPhysicalJordanSource_smul (a : ℂ) (U : E₄) :
    spectralPhysicalJordanSource (a • U)=a • spectralPhysicalJordanSource U := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralPhysicalJordanSource,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero]
  all_goals ring

theorem spectralPhysicalCircularField_add (νp νm eta : ℂ) (m : ℕ) (q : ℂ)
    (r : ℝ) (U V : E₄) :
    spectralPhysicalCircularField νp νm eta m q r (U+V)=
      spectralPhysicalCircularField νp νm eta m q r U+
        spectralPhysicalCircularField νp νm eta m q r V := by
  simp only [spectralPhysicalCircularField_regular,spectralRegularField_add]

theorem spectralPhysicalCircularField_smul (νp νm eta : ℂ) (m : ℕ) (q : ℂ)
    (r : ℝ) (a : ℂ) (U : E₄) :
    spectralPhysicalCircularField νp νm eta m q r (a • U)=
      a • spectralPhysicalCircularField νp νm eta m q r U := by
  simp only [spectralPhysicalCircularField_regular,spectralRegularField_smul]

theorem spectralPhysicalSource_combination (νp νm eta : ℂ) (m : ℕ) (q : ℂ)
    (D₁ D₂ : ℝ → E₄) (U₁ U₂ : E₄) (a b : ℂ) (r : ℝ)
    (hD₁ : HasDerivAt D₁ (spectralPhysicalCircularField νp νm eta m q r (D₁ r)+
      spectralPhysicalJordanSource U₁) r)
    (hD₂ : HasDerivAt D₂ (spectralPhysicalCircularField νp νm eta m q r (D₂ r)+
      spectralPhysicalJordanSource U₂) r) :
    HasDerivAt (fun s => a • D₁ s+b • D₂ s)
      (spectralPhysicalCircularField νp νm eta m q r (a • D₁ r+b • D₂ r)+
        spectralPhysicalJordanSource (a • U₁+b • U₂)) r := by
  apply ((hD₁.const_smul a).add (hD₂.const_smul b)).congr_deriv
  simp only [spectralPhysicalCircularField_add,spectralPhysicalCircularField_smul,
    spectralPhysicalJordanSource_add,spectralPhysicalJordanSource_smul,smul_add]
  abel

end DefocusingNLS

end OAI
