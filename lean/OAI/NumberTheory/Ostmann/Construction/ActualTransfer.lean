import OAI.NumberTheory.Ostmann.Construction.ActualOffDiagonal

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

theorem transfer_from_real_energy {a b : ℂ} {energy diagonal c : ℝ}
    (hbound : ‖a‖^2≤Real.exp (-c)*energy)
    (hsplit : (energy:ℂ)=(diagonal:ℂ)+b) :
    Real.exp c*‖a‖^2≤diagonal+‖b‖ := by
  have hre := congrArg Complex.re hsplit
  simp only [Complex.add_re,Complex.ofReal_re] at hre
  have hE : energy≤diagonal+‖b‖ := by rw [hre]; exact add_le_add (le_refl diagonal) (Complex.re_le_norm b)
  calc
    Real.exp c*‖a‖^2≤Real.exp c*(Real.exp (-c)*energy) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos c).le
    _ = energy := by rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
    _ ≤ _ := hE

theorem actualAmplitude_transfer_of_offDiagonal
    (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (hZ : 0<logCellMass G ∅) (bins : List ℕ→State→ℝ) (l : ℕ)
    (hoff : extendedOffDiagonal d P sources seed V (logCellPrimeSource G ∅ hZ) spectator m X G bins l=
      actualAmplitude sources seed V (logCellPrimeSource G ∅ hZ) spectator m X G
        (residueTransform d) (favorableGiantResidueTransform d P) bins (l+1)) :
    Real.exp (Real.log (logCellMass G ∅))*
      ‖actualAmplitude sources seed V (logCellPrimeSource G ∅ hZ) spectator m X G
        (residueTransform d) (favorableGiantResidueTransform d P) bins l‖^2≤
      extendedDiagonal d P sources seed V (logCellPrimeSource G ∅ hZ) spectator m X G bins l+
      ‖actualAmplitude sources seed V (logCellPrimeSource G ∅ hZ) spectator m X G
        (residueTransform d) (favorableGiantResidueTransform d P) bins (l+1)‖ := by
  apply transfer_from_real_energy
    (actualAmplitude_integer_row_bound d P sources seed V spectator m X G hZ bins l)
  rw [extendedRowEnergy_split,hoff]

end Ostmann.Construction

end

end OAI
