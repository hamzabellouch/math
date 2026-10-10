import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingTail

namespace OAI

/-! Subtraction of two solutions with the same physical source yields the homogeneous equation. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalCircularField_sub (νp νm eta : ℂ) (m : ℕ) (q : ℂ)
    (r : ℝ) (Z W : E₄) :
    spectralPhysicalCircularField νp νm eta m q r (Z-W)=
      spectralPhysicalCircularField νp νm eta m q r Z-
        spectralPhysicalCircularField νp νm eta m q r W := by
  have hh := show spectralPhysicalCircularField νp νm eta m q r (1 • Z+(-1 : ℂ) • W)=
      (1 : ℂ) • spectralPhysicalCircularField νp νm eta m q r Z+
        (-1 : ℂ) • spectralPhysicalCircularField νp νm eta m q r W by
    simp only [spectralPhysicalCircularField_regular,spectralRegularField_add,
      spectralRegularField_smul,one_smul]
  simpa only [one_smul,neg_one_smul,sub_eq_add_neg] using hh

theorem spectralPhysicalSource_subtraction (νp νm eta : ℂ) (m : ℕ) (q : ℂ)
    (Z W : ℝ → E₄) (S : E₄) (r : ℝ)
    (hZ : HasDerivAt Z (spectralPhysicalCircularField νp νm eta m q r (Z r)+S) r)
    (hW : HasDerivAt W (spectralPhysicalCircularField νp νm eta m q r (W r)+S) r) :
    HasDerivAt (fun s => Z s-W s)
      (spectralPhysicalCircularField νp νm eta m q r (Z r-W r)) r := by
  apply (hZ.sub hW).congr_deriv
  rw [spectralPhysicalCircularField_sub]
  abel

end DefocusingNLS

end OAI
