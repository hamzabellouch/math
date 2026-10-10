import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCoefficientMajorant

namespace OAI

/-! The actual dual coefficient bound becomes a product of a geometric
ramified factor and convergent norm powers. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def metaplecticRamifiedRatio (σ : ℝ) : ℝ := (3:ℝ)^(-2/3-σ)

lemma metaplectic_monomial_decay {H P W : ℝ} (hH : 0 < H) (hP : 0 < P) (hW : 0 < W)
    (σ : ℝ) (k : ℕ) :
    ((3:ℝ)^((k:ℝ)/3)*Real.sqrt P*(H*P))/
        (((3:ℝ)^((k:ℝ)-1)*H*W*P^3)^(1+σ)) =
      (3:ℝ)^(1+σ)*metaplecticRamifiedRatio σ^k*
        H^(-σ)*W^(-1-σ)*P^(-3/2-3*σ) := by
  have h3 : (3:ℝ)^((k:ℝ)/3)/(((3:ℝ)^((k:ℝ)-1))^(1+σ)) =
      (3:ℝ)^(1+σ)*metaplecticRamifiedRatio σ^k := by
    rw [←Real.rpow_mul (by norm_num),←Real.rpow_sub (by norm_num)]
    unfold metaplecticRamifiedRatio
    rw [←Real.rpow_mul_natCast (by norm_num),←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hH' : H/H^(1+σ) = H^(-σ) := by
    calc
      _ = H^(1:ℝ)/H^(1+σ) := by rw [Real.rpow_one]
      _ = H^(1-(1+σ)) := (Real.rpow_sub hH _ _).symm
      _ = _ := by congr 1; ring
  have hW' : 1/W^(1+σ) = W^(-1-σ) := by
    rw [one_div,←Real.rpow_neg hW.le]
    congr 1
    ring
  have hP' : (Real.sqrt P*P)/(P^3)^(1+σ) = P^(-3/2-3*σ) := by
    calc
      _ = (P^(1/2:ℝ)*P^(1:ℝ))/P^((3:ℝ)*(1+σ)) := by
        rw [Real.sqrt_eq_rpow,Real.rpow_one,←Real.rpow_natCast_mul hP.le]
        norm_num
      _ = P^((1/2+1)-(3:ℝ)*(1+σ)) := by
        rw [←Real.rpow_add hP,←Real.rpow_sub hP]
      _ = _ := by congr 1; ring
  rw [Real.mul_rpow (by positivity) (pow_nonneg hP.le _),
    Real.mul_rpow (by positivity) hW.le,
    Real.mul_rpow (by positivity) hH.le]
  calc
    _ = ((3:ℝ)^((k:ℝ)/3)/(((3:ℝ)^((k:ℝ)-1))^(1+σ)))*
        (H/H^(1+σ))*(1/W^(1+σ))*((Real.sqrt P*P)/(P^3)^(1+σ)) := by ring
    _ = _ := by rw [h3,hH',hW',hP']

lemma metaplecticRamifiedRatio_bounds {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ metaplecticRamifiedRatio σ ∧ metaplecticRamifiedRatio σ < 1 := by
  exact ⟨Real.rpow_nonneg (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩

/-- Decay of an actual nonzero Voronoi coefficient with its published
support representation. The free and cubed factors now have convergent
norm exponents. -/
theorem metaplectic_coefficient_decay
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {r : Eisenstein} (hr : primary r) (n : MetaplecticDualArgument)
    {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ) {h h' w : Eisenstein}
    (hh : primary h) (hh' : primary h') (hw : primary w) (hwr : IsCoprime w r)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3)
    (ha : ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) (σ : ℝ) :
    ‖a r n*metaplecticLocalCoefficient r n‖/
        (Complex.normSq (metaplecticFrequency n))^(1+σ) ≤
      C*(3:ℝ)^(1+σ)*metaplecticRamifiedRatio σ^((j+1).toNat)*
        norm h^(-σ)*norm w^(-1-σ)*norm h'^(-3/2-3*σ) := by
  let k := (j+1).toNat
  have hjk : (k:ℝ) = (j:ℝ)+1 := by
    dsimp [k]
    have hi : (((j+1).toNat:ℕ):ℤ) = j+1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hi
  have hmax : ((max j 0:ℤ):ℝ) ≤ k := by
    rw [hjk]
    exact_mod_cast (show max j 0 ≤ j+1 by omega)
  have h3 : (3:ℝ)^((max j 0:ℤ)/3:ℝ) ≤ (3:ℝ)^((k:ℝ)/3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hh0 := norm_nonneg h
  have hhp0 := norm_nonneg h'
  have hw0 := norm_nonneg w
  have hc := metaplectic_actual_coefficient_bound hC hr n hj ζ hh hh' hwr he ha
  have hc' : ‖a r n*metaplecticLocalCoefficient r n‖ ≤
      C*((3:ℝ)^((k:ℝ)/3)*Real.sqrt (norm h')*(norm h*norm h')) := by
    calc
      _ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*(norm h*norm h') := hc
      _ ≤ C*3^((k:ℝ)/3)*Real.sqrt (norm h')*(norm h*norm h') := by gcongr
      _ = _ := by ring
  have hn := metaplectic_frequency_norm n k ζ h h' w
    (metaplectic_numerator_of_frequency n hj ζ h h' w he)
  rw [hn]
  apply (div_le_div_of_nonneg_right hc' (by positivity)).trans_eq
  rw [mul_div_assoc,metaplectic_monomial_decay
    (norm_pos_of_ne_zero (primary_ne_zero hh))
    (norm_pos_of_ne_zero (primary_ne_zero hh'))
    (norm_pos_of_ne_zero (primary_ne_zero hw)) σ k]
  ring

end CubicFirstMoment

end

end OAI
