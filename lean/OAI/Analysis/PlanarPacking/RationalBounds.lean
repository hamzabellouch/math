import OAI.Analysis.PlanarPacking.Envelopes
import OAI.Analysis.PlanarPacking.AtomTail

namespace OAI

/-!
# Rational Fourier envelopes

Explicit rational majorants control the direct and transformed spectral envelopes
at integral and half-integral radii.
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
noncomputable def piUpper : ℝ := 31416/10000
lemma piUpper_pos : 0<piUpper := by norm_num [piUpper]
lemma pi_le_upper : Real.pi ≤ piUpper := pi_fine.2.le
noncomputable def pieceIntCap (j : Fin 6) (n : ℕ) : ℝ :=
  lambdaCap ⟨j.val,by omega⟩*pieceBase j^n*massRational j n
noncomputable def atomIntCap (j : Fin 7) (n : ℕ) : ℝ :=
  atomMass j*lambdaCap j*atomBase j^n
lemma pieceIntCap_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ pieceIntCap j n := by
  exact mul_nonneg (mul_nonneg (lambdaCap_nonneg _) (pow_nonneg (pieceBase_pos j).le n)) (massRational_nonneg _ _)
lemma atomIntCap_nonneg (j : Fin 7) (n : ℕ) : 0 ≤ atomIntCap j n := by
  exact mul_nonneg (mul_nonneg (by fin_cases j <;> norm_num [atomMass]) (lambdaCap_nonneg _)) (pow_nonneg (atomBase_pos j).le n)
lemma pieceL_le_intCap (j : Fin 6) (n : ℕ) : pieceL j n ≤ pieceIntCap j n := by
  exact mul_le_mul (mul_le_mul_of_nonneg_left (decay_pieceBase j n) (lambdaCap_nonneg _))
    (pieceMass_le j n) (pieceMass_nonneg _ (Nat.cast_nonneg n))
      (mul_nonneg (lambdaCap_nonneg _) (pow_nonneg (pieceBase_pos j).le n))
lemma atomL_le_intCap (j : Fin 7) (n : ℕ) : atomL j n ≤ atomIntCap j n := by
  exact mul_le_mul_of_nonneg_left (decay_atomBase j n)
    (mul_nonneg (by fin_cases j <;> norm_num [atomMass]) (lambdaCap_nonneg _))
noncomputable def directRational (ell : ℕ) : ℝ :=
  ∑ j : Fin 6,densityCap j/6*(piUpper*((j.val:ℝ)+1)/6)^ell
noncomputable def transformRational (ell n : ℕ) : ℝ :=
  ∑ j : Fin 6,densityCap j*pieceIntCap j n*(piUpper*zCap ⟨j.val,by omega⟩)^ell
noncomputable def atomicRational (ell n : ℕ) : ℝ :=
  ∑ j : Fin 7,atomIntCap j n*(piUpper*zCap j)^ell
lemma directEnvelope_le_rat (ell : ℕ) : directEnvelope ell ≤ directRational ell := by
  apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_left
  · apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right pi_le_upper (by positivity)) (by norm_num)
  · exact div_nonneg (densityCap_nonneg _) (by norm_num)
lemma transformEnvelope_le_rat (ell n : ℕ) : transformEnvelope ell n ≤ transformRational ell n := by
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pieceL_le_intCap j n) (densityCap_nonneg _))
    (pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le (zCap_nonneg _))
      (mul_le_mul_of_nonneg_right pi_le_upper (zCap_nonneg _)) ell)
    (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _)
    (mul_nonneg (densityCap_nonneg _) (pieceIntCap_nonneg _ _))
lemma atomicEnvelope_le_rat (ell n : ℕ) : atomicEnvelope ell n ≤ atomicRational ell n := by
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul (atomL_le_intCap j n)
    (pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le (zCap_nonneg _))
      (mul_le_mul_of_nonneg_right pi_le_upper (zCap_nonneg _)) ell)
    (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _)
    (atomIntCap_nonneg _ _)
noncomputable def taylorEnvelope (ell n : ℕ) : ℝ :=
  80*piUpper^ell+(23:ℝ)/10*transformRational ell n+(17:ℝ)/1000*atomicRational ell n
noncomputable def halfBase : Fin 6 → ℝ := ![21657/1000000,85318/1000000,243240/1000000,469014/1000000,703381/1000000,910487/1000000]
lemma halfBase_pos (j : Fin 6) : 0<halfBase j := by fin_cases j <;> norm_num [halfBase]
lemma halfBase_contains (j : Fin 6) :
    Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩/2) ≤ halfBase j := by
  have hh:=decay_pieceBase j 1
  norm_num only [Nat.cast_one,mul_one,pow_one] at hh
  have hs : Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩/2)^2 ≤ pieceBase j := by
    rw [← Real.exp_nat_mul]
    convert hh using 1; congr 1; ring
  have hb : pieceBase j ≤ halfBase j^2 := by fin_cases j <;> norm_num [pieceBase,halfBase]
  nlinarith [halfBase_pos j]
noncomputable def halfMass (j : Fin 6) : ℝ :=
  if slopeCap j=0 then 1/6 else min (1/6) (2/((314159/100000:ℝ)*slopeCap j))
lemma halfMass_nonneg (j : Fin 6) : 0 ≤ halfMass j := by
  fin_cases j <;> norm_num [halfMass,slopeCap]
lemma pieceMass_half (j : Fin 6) : pieceMass j (1/2) ≤ halfMass j := by
  unfold pieceMass halfMass
  by_cases hz : slopeCap j=0
  · simp [hz]
  · norm_num only [hz,ite_false,mul_eq_zero,one_div_ne_zero,OfNat.ofNat_ne_zero,false_or]
    apply min_le_min_left
    have hs : 0<slopeCap j := lt_of_le_of_ne (slopeCap_nonneg j) (Ne.symm hz)
    have hp:=one_div_le_one_div_of_le (by positivity : (0:ℝ)<(314159/100000)*slopeCap j/2)
      (show (314159/100000:ℝ)*slopeCap j/2 ≤ Real.pi*slopeCap j*(1/2) by nlinarith [pi_fine.1])
    convert hp using 1; field_simp
noncomputable def halfCap (j : Fin 6) : ℝ := lambdaCap ⟨j.val,by omega⟩*halfBase j*halfMass j
lemma pieceL_half (j : Fin 6) : pieceL j (1/2) ≤ halfCap j := by
  unfold pieceL halfCap
  have hb:=halfBase_contains j
  have hb' : Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*(1/2)) ≤ halfBase j := by
    convert hb using 1; congr 1; ring
  exact mul_le_mul (mul_le_mul_of_nonneg_left hb' (lambdaCap_nonneg _)) (pieceMass_half j)
    (pieceMass_nonneg _ (by norm_num)) (mul_nonneg (lambdaCap_nonneg _) (halfBase_pos j).le)
noncomputable def halfTransform (ell : ℕ) : ℝ :=
  ∑ j : Fin 6,densityCap j*halfCap j*(piUpper*zCap ⟨j.val,by omega⟩)^ell
lemma transformEnvelope_le_half (ell : ℕ) : transformEnvelope ell (1/2) ≤ halfTransform ell := by
  apply Finset.sum_le_sum; intro j _
  have hb : 0 ≤ halfCap j := mul_nonneg (mul_nonneg (lambdaCap_nonneg _) (halfBase_pos j).le) (halfMass_nonneg j)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pieceL_half j) (densityCap_nonneg _))
    (pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le (zCap_nonneg _))
      (mul_le_mul_of_nonneg_right pi_le_upper (zCap_nonneg _)) ell)
    (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _)
    (mul_nonneg (densityCap_nonneg _) hb)
end SharpPlanar

end OAI
