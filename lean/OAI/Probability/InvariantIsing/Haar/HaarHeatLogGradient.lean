import OAI.Probability.InvariantIsing.Haar.HaarHeatLogBarrier
import OAI.Probability.InvariantIsing.Haar.HaarHeatOrder
import OAI.Probability.InvariantIsing.Haar.CompactNegativeMinimum

namespace OAI

/-! Exponential decay of the logarithmic gradient of a positive polynomial heat orbit. -/
noncomputable section
open Matrix MvPolynomial Set
namespace InvariantIsing

theorem haarPolynomialHeat_log_gradient_bound {N d : ℕ} (p : haarPolynomialSpace N d)
    (ε C : ℝ) (hε : 0 < ε)
    (hp : ∀ U : SpecialOrthogonal N, ε ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    (hC : ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialGamma (p : MatrixPolynomial N) p) U ≤
        C*(haarPolynomialValue (p : MatrixPolynomial N) U)^2)
    {T : ℝ} (hT : 0 ≤ T) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarPolynomialGamma
      ((haarPolynomialHeat N d T p : haarPolynomialSpace N d) : MatrixPolynomial N)
      ((haarPolynomialHeat N d T p : haarPolynomialSpace N d) : MatrixPolynomial N)) U ≤
      C*Real.exp (-2*((N:ℝ)-2)*T)*
        (haarPolynomialValue ((haarPolynomialHeat N d T p : haarPolynomialSpace N d) : MatrixPolynomial N) U)^2 := by
  let q (s : ℝ) : MatrixPolynomial N := (haarPolynomialHeat N d s p : haarPolynomialSpace N d)
  let a (s : ℝ) := C*Real.exp (-2*((N:ℝ)-2)*s)
  let H (s : ℝ) (V : SpecialOrthogonal N) := haarPolynomialValue (haarHeatLogBarrier p C s) V
  let G (s : ℝ) (V : SpecialOrthogonal N) := haarPolynomialValue (haarPolynomialGamma (q s) (q s)) V
  obtain ⟨P,hP⟩ := haarPolynomialValue_bound (p : MatrixPolynomial N)
  have hlow (s : ℝ) (hs : 0 ≤ s) (V : SpecialOrthogonal N) : ε ≤ haarPolynomialValue (q s) V :=
    (haarPolynomialHeat_bounds p ε P hp (fun W => (le_abs_self _).trans (hP W)) hs V).1
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set (SpecialOrthogonal N)))).exists_bound_of_continuousOn
    (continuous_haarPolynomialHeat_gamma p).continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (0,1) ⟨⟨le_rfl,hT⟩,mem_univ _⟩)
  have hGB (s : ℝ) (hs : s ∈ Icc (0:ℝ) T) (V : SpecialOrthogonal N) : G s V ≤ B :=
    (le_abs_self _).trans (hB (s,V) ⟨hs,mem_univ _⟩)
  let A := 2*|((N:ℝ)-2)|+2*B/ε^2+1
  let W (s : ℝ) (V : SpecialOrthogonal N) := Real.exp (-A*s)*H s V
  let D (s : ℝ) (V : SpecialOrthogonal N) :=
    -2*((N:ℝ)-2)*a s*(haarPolynomialValue (q s) V)^2+
      2*a s*haarPolynomialValue (q s) V*haarPolynomialValue (haarPolynomialLaplacian N (q s)) V-
      2*haarPolynomialValue (haarPolynomialGamma (q s) (haarPolynomialLaplacian N (q s))) V
  let Wt (z : ℝ × SpecialOrthogonal N) := Real.exp (-A*z.1)*(D z.1 z.2-A*H z.1 z.2)
  have hc : Continuous (fun z : ℝ × SpecialOrthogonal N => W z.1 z.2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
      (continuous_haarHeatLogBarrier p C)
  have hi (V : SpecialOrthogonal N) : 0 ≤ W 0 V := by
    simp only [W,H,haarHeatLogBarrier,haarPolynomialHeat_zero,mul_zero,Real.exp_zero,mul_one,one_mul]
    change 0 ≤ matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ) (haarLogBarrier p C)
    rw [haarLogBarrier_eval]
    exact sub_nonneg.mpr (hC V)
  have hd (s : ℝ) (_ : s ∈ Ioc (0:ℝ) T) (V : SpecialOrthogonal N) :
      HasDerivAt (fun r => W r V) (Wt (s,V)) s := by
    have he : HasDerivAt (fun r => Real.exp (-A*r)) (-A*Real.exp (-A*s)) s := by
      convert ((hasDerivAt_id s).const_mul (-A)).exp using 1
      all_goals simp only [id_eq,mul_one]
      all_goals ring
    have hh := haarHeatLogBarrier_hasDerivAt p C s V
    convert he.mul hh using 1
    all_goals dsimp only [Wt,D,H,q,a]
    all_goals ring
  have hmin (s : ℝ) (hs : s ∈ Ioc (0:ℝ) T) (V : SpecialOrthogonal N)
      (hneg : W s V < 0) (hm : ∀ Z, W s V ≤ W s Z) : 0 < Wt (s,V) := by
    have hHneg : H s V < 0 := by
      have he := Real.exp_pos (-A*s)
      dsimp only [W] at hneg
      nlinarith
    have hHmin (Z : SpecialOrthogonal N) : H s V ≤ H s Z :=
      (mul_le_mul_iff_right₀ (Real.exp_pos (-A*s))).mp (hm Z)
    have hu : 0 < haarPolynomialValue (q s) V := hε.trans_le (hlow s hs.1.le V)
    have hD : (-2*((N:ℝ)-2)+2*G s V/(haarPolynomialValue (q s) V)^2)*H s V ≤ D s V :=
      haarLogBarrier_min_derivative_lower (q s) (a s) V hu.ne' hHmin
    have hw : G s V/(haarPolynomialValue (q s) V)^2 ≤ B/ε^2 := by
      calc
        _ ≤ B/(haarPolynomialValue (q s) V)^2 :=
          div_le_div_of_nonneg_right (hGB s ⟨hs.1.le,hs.2⟩ V) (sq_nonneg _)
        _ ≤ B/ε^2 := div_le_div_of_nonneg_left hB0 (sq_pos_of_pos hε)
          ((sq_le_sq₀ hε.le hu.le).mpr (hlow s hs.1.le V))
    have hcoef : -2*((N:ℝ)-2)+2*G s V/(haarPolynomialValue (q s) V)^2 ≤ A-1 := by
      dsimp only [A]
      linear_combination 2*hw+2*(neg_le_abs ((N:ℝ)-2))
    have hmulf := mul_le_mul_of_nonpos_right hcoef hHneg.le
    have hstrict : 0 < D s V-A*H s V := by nlinarith
    exact mul_pos (Real.exp_pos (-A*s)) hstrict
  have hz := compact_nonneg_of_negative_min_derivative hT W Wt hc.continuousOn hi hd hmin
    T ⟨hT,le_rfl⟩ U
  have hH : 0 ≤ H T U := (mul_nonneg_iff_of_pos_left (Real.exp_pos (-A*T))).mp hz
  change 0 ≤ matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ)
    (haarLogBarrier (q T) (a T)) at hH
  rw [haarLogBarrier_eval] at hH
  exact sub_nonneg.mp hH

end InvariantIsing

end

end OAI
