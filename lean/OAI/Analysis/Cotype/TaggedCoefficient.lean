import OAI.Analysis.Cotype.GrowthCoefficient

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {k m : ℕ}

theorem sign_bitEquiv_symm (z : ZMod 2) : sign (bitEquiv.symm z) = binarySign z := by
  obtain ⟨b,rfl⟩ := bitEquiv.surjective z
  rw [Equiv.symm_apply_apply]
  cases b <;> simp [bitEquiv, binaryBit, sign]

def freePairingPattern (u v : Fin m → Cube k) : SignMatrix m := fun ij =>
  bitEquiv.symm (coordinateDual (cubeBinaryEquiv k (v ij.2)) (cubeBinaryEquiv k (u ij.1)))

theorem freePairingPattern_sign (u v : Fin m → Cube k) (i j : Fin m) :
    sign (freePairingPattern u v (i,j)) = character (v j) (u i) := by
  rw [freePairingPattern, sign_bitEquiv_symm, character_binary_dot]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T (k+m+m) m Dg Df)

def coefficientPrimal (ε : Cube m) (u : Fin m → Cube k) : GrowthSpace (k+m+m) X :=
  d.P (taggedPrimal u) ε

def coefficientDual (P : SignMatrix m) (δ : Cube m) (v : Fin m → Cube k) :
    GrowthSpace (k+m+m) Y →L[ℝ] ℝ :=
  average (fun D : SignMatrix m => character P D • d.Z (taggedDual v D) δ)

theorem coefficientPrimal_norm (ε : Cube m) (u : Fin m → Cube k) :
    ‖d.coefficientPrimal ε u‖ ≤ 1 := d.P_norm _ _

theorem coefficientDual_norm (P : SignMatrix m) (δ : Cube m) (v : Fin m → Cube k) :
    ‖d.coefficientDual P δ v‖ ≤ 1 := by
  calc
    _ ≤ average (fun D : SignMatrix m => ‖character P D • d.Z (taggedDual v D) δ‖) := norm_average_le _
    _ ≤ average (fun _ : SignMatrix m => (1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_smul, Real.norm_eq_abs, abs_character_finite, one_mul]
      exact d.Z_norm _ _
    _ = 1 := average_const_real _

theorem tagged_coefficient_extraction (hn : m+m ≤ k+m+m) (P : SignMatrix m)
    (ε δ : Cube m) (u v : Fin m → Cube k) :
    d.coefficientDual P δ v (d.amplifiedOperator (d.coefficientPrimal ε u)) =
      fourier (fun S => d.patternPairing hn S ε δ) P * character P (freePairingPattern u v) := by
  have he (D : SignMatrix m) : d.tuplePairing (taggedPrimal u) (taggedDual v D) ε δ =
      d.patternPairing hn (xorCube (freePairingPattern u v) D) ε δ := by
    apply (d.patternPairing_eq hn _ _ _ (taggedPrimal_frame u) (taggedDual_frame v D) _ ε δ).symm
    intro i j
    rw [taggedFrames_pairing]
    change _ = sign (Bool.xor (freePairingPattern u v (i,j)) (D (i,j)))
    rw [sign_xor, freePairingPattern_sign]
  calc
    _ = average (fun D : SignMatrix m => character P D *
        d.tuplePairing (taggedPrimal u) (taggedDual v D) ε δ) := by
      simp [coefficientDual, coefficientPrimal, tuplePairing, average]
    _ = fourier (fun D => d.patternPairing hn (xorCube (freePairingPattern u v) D) ε δ) P := by
      simp only [he, fourier]
      congr 1; funext D; ring
    _ = _ := fourier_translate (fun S => d.patternPairing hn S ε δ) _ P

end GrowthPairingData

end Cotype

end

end OAI
