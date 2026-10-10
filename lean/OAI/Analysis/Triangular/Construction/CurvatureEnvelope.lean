import OAI.Analysis.Triangular.Construction.CurvatureAnalytic
import OAI.Analysis.Triangular.Taylor.CoefficientSpectral
import OAI.Analysis.Triangular.Construction.CurvatureSums

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

def finiteCurvatureCap (br : Fin 2) : Fin 5 → ℝ :=
  if br.val=0 then ![828/10,44164/1000,23561/1000,9147/1000000,43834/1000000000]
  else ![291294/100,45877/1000,3893/1000,635/10000000000,167/100000000000000]
def finiteCurvatureEnvelope : Fin 5 → ℝ := ![1510,46,14,465/100000,23/1000000]
def tailCurvatureEnvelope : Fin 5 → ℝ := ![26500,1160,800,800,800]
lemma finiteCurvatureCap_bound (br : Fin 2) (i : Fin 5) (c : Fin 22) :
    rawCurvatureColumn br (curvaturePoint i) c≤finiteCurvatureCap br i := by
  fin_cases br <;> fin_cases i
  all_goals first
    | exact (curvatureColumn0_0_bound c).le | exact (curvatureColumn0_1_bound c).le
    | exact (curvatureColumn0_2_bound c).le | exact (curvatureColumn0_3_bound c).le
    | exact (curvatureColumn0_4_bound c).le | exact (curvatureColumn1_0_bound c).le
    | exact (curvatureColumn1_1_bound c).le | exact (curvatureColumn1_2_bound c).le
    | exact (curvatureColumn1_3_bound c).le | exact (curvatureColumn1_4_bound c).le
lemma finiteCurvatureCap_sum (i : Fin 5) :
    (finiteCurvatureCap 0 i+finiteCurvatureCap 1 i)/2≤finiteCurvatureEnvelope i := by
  fin_cases i <;> norm_num [finiteCurvatureCap,finiteCurvatureEnvelope]
lemma finiteCurvatureCap_nonneg (br : Fin 2) (i : Fin 5) : 0≤finiteCurvatureCap br i := by
  fin_cases br <;> fin_cases i <;> norm_num [finiteCurvatureCap]
lemma rawCurvatureColumn_antitone (br : Fin 2) (c : Fin 22) {u s : ℝ} (hus : u≤ s) :
    rawCurvatureColumn br s c≤rawCurvatureColumn br u c := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (curvatureWave_antitone 1 br (abs_le.mpr (frequency_mem j)) hus) (norm_nonneg _)
lemma finiteSpectral_curvature (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (i : Fin 5) {s : ℝ} (hs : curvaturePoint i≤ s) :
    ‖finiteSpectral (coefficientInput C a w) (waveFunctionJet 1 br 2 s)‖≤‖a‖*finiteCurvatureCap br i := by
  apply finiteSpectral_wave_bound
  intro c
  exact (rawCurvatureColumn_antitone br c hs).trans (finiteCurvatureCap_bound br i c)
def tailCurvatureCap (br : Fin 2) (i : Fin 5) : ℝ :=
  curvatureWave 0 br (curvaturePoint i) (if br.val=1 ∧ i.val=0 then 0 else 5/6)
lemma tailCurvatureCap_nonneg (br : Fin 2) (i : Fin 5) : 0≤tailCurvatureCap br i := curvatureWave_nonneg _ _ _ _
lemma tailCurvatureCap_bound (br : Fin 2) (i : Fin 5) {s t : ℝ}
    (hs : curvaturePoint i≤ s) (ht : |t|≤5/6) : curvatureWave 0 br s t≤tailCurvatureCap br i := by
  apply (curvatureWave_antitone 0 br ht hs).trans
  fin_cases br
  · exact curvature_tail_direct ht
  · by_cases hi : i=0
    · subst i
      exact curvature_tail_zero ht
    · have hu : 1≤curvaturePoint i := by fin_cases i <;> norm_num [curvaturePoint] at *
      have hval : ¬i.val=0 := by simpa only [Fin.val_eq_zero_iff] using hi
      simp only [tailCurvatureCap,true_and,hval,↓reduceIte]
      convert curvature_tail_positive hu ht using 1 <;> rfl
lemma tailCurvatureCap_sum (i : Fin 5) :
    (119/2)*(tailCurvatureCap 0 i+tailCurvatureCap 1 i)≤tailCurvatureEnvelope i := by
  have he : 60*(tailCurvatureCap 0 i+tailCurvatureCap 1 i)=rawTailCurvature i := by
    fin_cases i <;> norm_num [tailCurvatureCap,rawTailCurvature,frequency]
  have hb : rawTailCurvature i<tailCurvatureEnvelope i := by
    fin_cases i
    · exact curvatureTail0_bound
    · exact curvatureTail1_bound
    · exact curvatureTail2_bound
    · exact curvatureTail3_bound
    · exact curvatureTail4_bound
  nlinarith [tailCurvatureCap_nonneg 0 i,tailCurvatureCap_nonneg 1 i]
lemma tailSpectral_curvature (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (i : Fin 5) {s : ℝ} (hs : curvaturePoint i≤ s) :
    ‖tailSpectral (coefficientInput 0 a w) (waveFunctionJet 0 br 2 s)‖≤119*‖w‖*tailCurvatureCap br i := by
  exact ((tailSpectral _).le_opNorm _).trans (mul_le_mul (tailSpectral_zero_constant_norm a w)
    (waveFunctionJet_uniform _ _ _ (tailCurvatureCap_nonneg br i) (fun t ht => tailCurvatureCap_bound br i hs ht))
    (norm_nonneg _) (by positivity))
lemma pairJ_curvature (a b : TrigonometricCoefficients) (w v : TailCoefficients)
    (i : Fin 5) {s aL aT : ℝ} (hs : curvaturePoint i≤ s)
    (ha : ‖a‖≤aL) (hb : ‖b‖≤aL) (hw : ‖w‖≤aT) (hv : ‖v‖≤aT) :
    |iteratedDeriv 2 (pairJ (coefficientInput 0 a w) (coefficientInput 0 b v)) s|/2≤
      aL*finiteCurvatureEnvelope i+aT*tailCurvatureEnvelope i := by
  rw [←pairJJet_iterated]
  have hTa := tailSpectral_curvature a w 0 i hs
  have hTb := tailSpectral_curvature b v 1 i hs
  have hLa := finiteSpectral_curvature 0 a w 0 i hs
  have hLb := finiteSpectral_curvature 0 b v 1 i hs
  have hh := Complex.abs_re_le_norm (pairJJet (coefficientInput 0 a w) (coefficientInput 0 b v) 2 s)
  have hN := norm_add_le (inputJJet (coefficientInput 0 a w) 0 2 s) (inputJJet (coefficientInput 0 b v) 1 2 s)
  have hNa := norm_add_le (tailSpectral (coefficientInput 0 a w) (waveFunctionJet 0 0 2 s)) (finiteSpectral (coefficientInput 0 a w) (waveFunctionJet 1 0 2 s))
  have hNb := norm_add_le (tailSpectral (coefficientInput 0 b v) (waveFunctionJet 0 1 2 s)) (finiteSpectral (coefficientInput 0 b v) (waveFunctionJet 1 1 2 s))
  have hL0 := mul_le_mul_of_nonneg_right ha (finiteCurvatureCap_nonneg 0 i)
  have hL1 := mul_le_mul_of_nonneg_right hb (finiteCurvatureCap_nonneg 1 i)
  have hT0 := mul_le_mul_of_nonneg_right hw (tailCurvatureCap_nonneg 0 i)
  have hT1 := mul_le_mul_of_nonneg_right hv (tailCurvatureCap_nonneg 1 i)
  have hLf := mul_le_mul_of_nonneg_left (finiteCurvatureCap_sum i) ((norm_nonneg a).trans ha)
  have hTf := mul_le_mul_of_nonneg_left (tailCurvatureCap_sum i) ((norm_nonneg w).trans hw)
  change |(pairJJet _ _ 2 s).re|/2≤_
  dsimp only [pairJJet,inputJJet] at hh hN ⊢
  nlinarith
end AtomicTriangular.Construction
end

end OAI
