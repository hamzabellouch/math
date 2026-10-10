import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryBottom
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLowerCuspPositive

namespace OAI

/-! The three translated inversion types needed for primary bottom rows.
The actual constant is retained at the trivial type. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaFullTranslation_add (a b : Eisenstein) :
    cubicThetaFullTranslation (a+b)=cubicThetaFullTranslation a*cubicThetaFullTranslation b := by
  apply Subtype.ext
  change (!![1,a+b;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)=!![1,a;0,1]*!![1,b;0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

lemma cubicThetaShiftedInversion_factor (b : Eisenstein) :
    cubicThetaShiftedInversion b=cubicThetaFullTranslation b*cubicThetaFullInversion := by
  apply Subtype.ext
  change (!![b,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)=!![1,b;0,1]*!![0,-1;1,0]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

lemma cubicThetaNormalizedSeries_integer_translation (m : ℤ) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaFullTranslation (m:Eisenstein) • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  let u : SL(2,ℤ) := ⟨!![1,m;0,1],by simp [Matrix.det_fin_two]⟩
  have he : cubicThetaIntegerEmbedding u=cubicThetaFullTranslation (m:Eisenstein) := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change ((u i j:ℤ):Eisenstein)=(cubicThetaFullTranslation (m:Eisenstein)) i j
    fin_cases i <;> fin_cases j <;> norm_num [u,cubicThetaFullTranslation]
  rw [←he]
  exact cubicThetaNormalizedSeries_integer u p

lemma cubicThetaNormalizedSeries_triple_translation (b : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaFullTranslation (3*b) • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  have he : cubicThetaFullTranslation (3*b)=(cubicThetaPrincipalTranslation b).val := rfl
  rw [he]
  change cubicThetaNormalizedSeriesSection.val (cubicThetaPrincipalTranslation b • p)=_
  rw [cubicThetaNormalizedSeriesSection.property,cubicThetaPrincipalTranslation_value,one_mul]

lemma cubicThetaNormalizedSeries_shifted_trivial (m n : ℤ) (hn : (3:ℤ) ∣ n)
    (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val
      (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE) • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  obtain ⟨t,rfl⟩ := hn
  have he : (m:Eisenstein)+((3*t:ℤ):Eisenstein)*omegaE=
      (m:Eisenstein)+3*((t:Eisenstein)*omegaE) := by push_cast; ring
  rw [he,cubicThetaShiftedInversion_factor,cubicThetaFullTranslation_add,mul_smul,mul_smul,
    cubicThetaNormalizedSeries_integer_translation,cubicThetaNormalizedSeries_triple_translation,
    cubicThetaNormalizedSeriesSection_inversion]

lemma cubicThetaNormalizedSeries_shifted_nontrivial (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val
      (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE) • p)=
      cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient n) p.val := by
  change cubicThetaArithmeticBaseScalar⁻¹*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex
        (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE))) p.val)=_
  rw [cubicThetaShiftedPositiveSeries_common m n hn p.property p.val.1,←mul_assoc,
    inv_mul_cancel₀ cubicThetaArithmeticBaseScalar_ne_zero,one_mul]

def cubicThetaCuspExpansion (n : ℤ) (p : ℂ×ℝ) : ℂ :=
  if (3:ℤ) ∣ n then
    cubicThetaSeriesConstant*((p.2^(2/3:ℝ):ℝ):ℂ)+
      cubicThetaNonconstant cubicThetaArithmeticCoefficient p
  else cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient n) p

theorem cubicThetaNormalizedSeries_shifted_complete (m n : ℤ) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val
      (cubicThetaShiftedInversion ((m:Eisenstein)+n*omegaE) • p)=
      cubicThetaCuspExpansion n p.val := by
  by_cases hn : (3:ℤ) ∣ n
  · rw [cubicThetaNormalizedSeries_shifted_trivial m n hn p,cubicThetaCuspExpansion,ite_eq_left hn]
    exact cubicThetaNormalizedSeriesSection_apply p
  · rw [cubicThetaNormalizedSeries_shifted_nontrivial m n hn p,cubicThetaCuspExpansion,ite_eq_right hn]

theorem cubicThetaNormalizedSeries_primaryBottom_complete (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (m n : ℤ) (ha : g 0 0=(m:Eisenstein)+n*omegaE)
    (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (g • p)=
      cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)*
        cubicThetaCuspExpansion n (cubicThetaFullTranslation (g 1 1) • p).val := by
  rw [cubicThetaNormalizedSeries_primaryBottom g hc p,ha,
    cubicThetaNormalizedSeries_shifted_complete]

end CubicFirstMoment

end

end OAI
