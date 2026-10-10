import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeModelMass
import OAI.NumberTheory.CubicMoment.Estimates.MoebiusDensityTail
import OAI.NumberTheory.CubicMoment.Estimates.FiniteSieveDensity

namespace OAI

/-! Quantitative identification of the ordinary squarefree model mass
with the finite density in the positive variance term. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma squarefree_density_scale {A : ℝ} (hA : 1 ≤ A) {B : ℝ} (hB : 1 ≤ B) :
    (Real.sqrt (B*A))^(-(1/2:ℝ)) ≤ A^(-(1/4:ℝ)) := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  calc
    _ ≤ (Real.sqrt A)^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_nonpos
      (Real.sqrt_pos.mpr hAp) (Real.sqrt_le_sqrt (by nlinarith)) (by norm_num)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hAp.le]
      norm_num

theorem UniformLogWeights.squarefreeModelMass_density_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i A D, 1 ≤ A → 1 ≤ D →
      ‖squarefreeModelMass (W i) A-
        ((A^(2/3:ℝ)*(2*Real.pi/(9*Real.sqrt 3)):ℝ):ℂ)*mellin (W i) (2/3)*
          (finiteSieveDensity (squarefreeDivisorTruncation D):ℂ)‖ ≤
        K*(A^(5/12:ℝ)+A^(2/3:ℝ)*D^(-(1/2:ℝ))) := by
  obtain ⟨C,hC,hfinite⟩ := h.squarefreeModelMass_finite_error
  obtain ⟨E,hE,hEuler⟩ := radialEulerPartial_one_error
  obtain ⟨F,hF,hSieve⟩ := finiteSieveDensity_error
  obtain ⟨M,hM,hMellin⟩ := h.mellin_decay 1 0
  let P := |2*Real.pi/(9*Real.sqrt 3)| * M
  let K := C+P*(E+F)+1
  have hP : 0 ≤ P := mul_nonneg (abs_nonneg _) hM.le
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro i A D hA hD
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hDp : 0 < D := zero_lt_one.trans_le hD
  let B := Real.exp (h.realPower (-1/3)).radius
  let T := Real.sqrt (B*A)
  let ρ : ℂ := ((∑' a : Eisenstein,moebiusResidueTerm a):ℝ)
  let J : ℂ := ((A^(2/3:ℝ)*(2*Real.pi/(9*Real.sqrt 3)):ℝ):ℂ)*mellin (W i) (2/3)
  have hB : 1 ≤ B := Real.one_le_exp (h.realPower (-1/3)).radius_nonneg
  have hT : 0 < T := Real.sqrt_pos.mpr (mul_pos (zero_lt_one.trans_le hB) hAp)
  have hscale : T^(-(1/2:ℝ)) ≤ A^(-(1/4:ℝ)) := squarefree_density_scale hA hB
  have he : ‖metaplecticRadialEulerPartial 1 T-ρ‖ ≤ E*A^(-(1/4:ℝ)) :=
    (hEuler T hT).trans (mul_le_mul_of_nonneg_left hscale hE.le)
  have hs : ‖ρ-(finiteSieveDensity (squarefreeDivisorTruncation D):ℂ)‖ ≤
      F*D^(-(1/2:ℝ)) := by
    dsimp [ρ]
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
    exact hSieve D hD
  have hd : ‖metaplecticRadialEulerPartial 1 T-
      (finiteSieveDensity (squarefreeDivisorTruncation D):ℂ)‖ ≤
      E*A^(-(1/4:ℝ))+F*D^(-(1/2:ℝ)) := by
    calc
      _ = ‖(metaplecticRadialEulerPartial 1 T-ρ)+
          (ρ-(finiteSieveDensity (squarefreeDivisorTruncation D):ℂ))‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add he hs)
  have hm : ‖mellin (W i) (2/3)‖ ≤ M := by
    simpa using hMellin i (2/3) (by norm_num) 0
  have hJ : ‖J‖ ≤ P*A^(2/3:ℝ) := by
    dsimp [J,P]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hAp.le _)]
    calc
      _ ≤ A^(2/3:ℝ)*|2*Real.pi/(9*Real.sqrt 3)| * M :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by ring
  have ha : A^(1/6:ℝ) ≤ A^(5/12:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hp : A^(2/3:ℝ)*A^(-(1/4:ℝ)) = A^(5/12:ℝ) := by
    rw [←Real.rpow_add hAp]
    norm_num
  calc
    _ = ‖(squarefreeModelMass (W i) A-J*metaplecticRadialEulerPartial 1 T)+
        J*(metaplecticRadialEulerPartial 1 T-
          (finiteSieveDensity (squarefreeDivisorTruncation D):ℂ))‖ := by dsimp [J]; congr 1; ring
    _ ≤ C*A^(1/6:ℝ)+‖J‖*‖metaplecticRadialEulerPartial 1 T-
        (finiteSieveDensity (squarefreeDivisorTruncation D):ℂ)‖ := by
      apply (norm_add_le _ _).trans
      rw [norm_mul]
      exact add_le_add (hfinite i A hAp) le_rfl
    _ ≤ C*A^(5/12:ℝ)+(P*A^(2/3:ℝ))*
        (E*A^(-(1/4:ℝ))+F*D^(-(1/2:ℝ))) := by
      exact add_le_add (mul_le_mul_of_nonneg_left ha hC.le)
        (mul_le_mul hJ hd (_root_.norm_nonneg _) (by positivity))
    _ = (C+P*E)*A^(5/12:ℝ)+P*F*(A^(2/3:ℝ)*D^(-(1/2:ℝ))) := by
      calc
        _ = C*A^(5/12:ℝ)+P*E*(A^(2/3:ℝ)*A^(-(1/4:ℝ)))+
            P*F*(A^(2/3:ℝ)*D^(-(1/2:ℝ))) := by ring
        _ = _ := by rw [hp]; ring
    _ ≤ K*(A^(5/12:ℝ)+A^(2/3:ℝ)*D^(-(1/2:ℝ))) := by
      rw [mul_add]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [K]
        nlinarith
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [K]
        nlinarith

end CubicFirstMoment

end

end OAI
