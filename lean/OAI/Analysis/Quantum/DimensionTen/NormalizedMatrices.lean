import OAI.Analysis.Quantum.DimensionTen.Annihilator

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

def NB (i : Fin 3) : Matrix (Fin 20) (Fin 20) ℚ :=
  ((d : ℚ)⁻¹) • ((![B0, B1, B2] i).map (Int.castRingHom ℚ))

def eQ (i : Fin 20) : Fin 20 → ℚ := Pi.single i 1

lemma dQ_ne_zero : (d : ℚ) ≠ 0 := by norm_num [d, PencilAlgebra.denominator]

lemma cast_mulVec (B : Matrix (Fin 20) (Fin 20) ℤ) (v : Fin 20 → ℤ) :
    (fun j => ((B *ᵥ v) j : ℚ)) = B.map (Int.castRingHom ℚ) *ᵥ (fun j => (v j : ℚ)) := by
  ext j
  exact (Int.castRingHom ℚ).map_mulVec B v j

lemma cast_single (i : Fin 20) :
    (fun j => ((Pi.single i 1 : Fin 20 → ℤ) j : ℚ)) = eQ i := by
  ext j
  simp [eQ, Pi.single_apply]

lemma normalize_shift (B : Matrix (Fin 20) (Fin 20) ℤ) (i j : Fin 20)
    (h : B *ᵥ Pi.single i 1 = d • Pi.single j 1) :
    ((d : ℚ)⁻¹ • B.map (Int.castRingHom ℚ)) *ᵥ eQ i = eQ j := by
  have hh := congrArg (fun v : Fin 20 → ℤ => fun k => (v k : ℚ)) h
  rw [cast_mulVec, cast_single] at hh
  have hcast : (fun k => ((d • (Pi.single j 1 : Fin 20 → ℤ)) k : ℚ)) = (d : ℚ) • eQ j := by
    ext k
    simp [eQ, Pi.single_apply, smul_eq_mul]
  rw [hcast] at hh
  rw [Matrix.smul_mulVec, hh, smul_smul, inv_mul_cancel₀ dQ_ne_zero, one_smul]

lemma NB_commute (i j : Fin 3) : Commute (NB i) (NB j) := by
  change Commute ((d : ℚ)⁻¹ • _) ((d : ℚ)⁻¹ • _)
  apply Commute.smul_right
  apply Commute.smul_left
  have h01 : Commute (B0.map (Int.castRingHom ℚ)) (B1.map (Int.castRingHom ℚ)) :=
    (show Commute B0 B1 from commute_01).map (Int.castRingHom ℚ).mapMatrix
  have h02 : Commute (B0.map (Int.castRingHom ℚ)) (B2.map (Int.castRingHom ℚ)) :=
    (show Commute B0 B2 from commute_02).map (Int.castRingHom ℚ).mapMatrix
  have h12 : Commute (B1.map (Int.castRingHom ℚ)) (B2.map (Int.castRingHom ℚ)) :=
    (show Commute B1 B2 from commute_12).map (Int.castRingHom ℚ).mapMatrix
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact h01
  · exact h02
  · exact h01.symm
  · exact Commute.refl _
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact Commute.refl _

lemma QB_annihilator : aeval (B0.map (Int.castRingHom ℚ)) (F.map (algebraMap ℤ ℚ)) = 0 := by
  rw [Polynomial.aeval_map_algebraMap, aeval_F]
  have h := congrArg (Int.castRingHom ℚ).mapMatrix FP_B0
  simpa only [map_FP, map_zero, RingHom.mapMatrix_apply] using h

end DimensionTen.Border

end
end

end OAI
