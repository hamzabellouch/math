import OAI.NumberTheory.CubicMoment.Theta.CubicThetaVerticalSeriesDerivative
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalSeriesDerivative
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace OAI

/-! The actual differential of each theta term in the full upper half-space. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaTraceCLM (w : ℂ) : ℂ →L[ℝ] ℝ :=
  (2:ℝ) • (Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ w))

lemma cubicThetaTraceCLM_apply (w z : ℂ) : cubicThetaTraceCLM w z=tracePair w z := rfl

def cubicThetaSeriesTermFDeriv (a : Eisenstein → ℂ) (p : ℂ × ℝ) (n : Eisenstein) :
    (ℂ × ℝ) →L[ℝ] ℂ :=
  ((cubicThetaTraceCLM (cubicThetaFrequency n)).comp (ContinuousLinearMap.fst ℝ ℂ ℝ)).smulRight
    (2*Real.pi*Complex.I*cubicThetaSeriesTerm a p.1 p.2 n)+
  (ContinuousLinearMap.snd ℝ ℂ ℝ).smulRight (cubicThetaSeriesTermVertical a p.1 p.2 n)

lemma cubicThetaSeriesTermFDeriv_apply (a : Eisenstein → ℂ) (p : ℂ × ℝ)
    (n : Eisenstein) (q : ℂ × ℝ) :
    cubicThetaSeriesTermFDeriv a p n q=
      (tracePair (cubicThetaFrequency n) q.1:ℂ)*
        (2*Real.pi*Complex.I*cubicThetaSeriesTerm a p.1 p.2 n)+
      (q.2:ℂ)*cubicThetaSeriesTermVertical a p.1 p.2 n := by
  simp only [cubicThetaSeriesTermFDeriv,add_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
    cubicThetaTraceCLM_apply,Complex.real_smul]

theorem cubicThetaSeriesTerm_hasFDerivAt (a : Eisenstein → ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) (n : Eisenstein) :
    HasFDerivAt (fun q : ℂ × ℝ => cubicThetaSeriesTerm a q.1 q.2 n)
      (cubicThetaSeriesTermFDeriv a p n) p := by
  by_cases hn : n=0
  · have he : (fun q : ℂ × ℝ => cubicThetaSeriesTerm a q.1 q.2 n)=fun _ => 0 := by
      funext q
      simp only [cubicThetaSeriesTerm,hn,ite_true]
    rw [he]
    have hz : cubicThetaSeriesTermFDeriv a p n=0 := by
      apply ContinuousLinearMap.ext
      intro q
      simp [cubicThetaSeriesTermFDeriv_apply,cubicThetaSeriesTerm,cubicThetaSeriesTermVertical,hn]
    rw [hz]
    exact hasFDerivAt_const (c:=(0:ℂ)) p
  let L : (ℂ × ℝ) →L[ℝ] ℝ :=
    (cubicThetaTraceCLM (cubicThetaFrequency n)).comp (ContinuousLinearMap.fst ℝ ℂ ℝ)
  let H : (ℂ × ℝ) →L[ℝ] ℝ := ‖cubicThetaFrequency n‖ • (ContinuousLinearMap.snd ℝ ℂ ℝ)
  have hw := (cubicThetaWhittaker_hasDerivAt (mul_pos (cubicThetaFrequency_pos hn) hp)).hasFDerivAt.comp p H.hasFDerivAt
  have hc := (Real.hasDerivAt_fourierChar (tracePair (cubicThetaFrequency n) p.1)).hasFDerivAt.comp p L.hasFDerivAt
  have h := (hw.const_mul (a n)).mul hc
  convert! h using 1
  · funext q
    simp [cubicThetaSeriesTerm,hn,H,L,cubicThetaTraceCLM_apply,Function.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  · apply ContinuousLinearMap.ext
    intro q
    simp [cubicThetaSeriesTermFDeriv_apply,cubicThetaSeriesTerm,cubicThetaSeriesTermVertical,
      hn,H,L,cubicThetaTraceCLM_apply,Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,Complex.real_smul,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring

lemma cubicThetaSeriesTermFDeriv_norm_le (a : Eisenstein → ℂ) (p : ℂ × ℝ) (n : Eisenstein) :
    ‖cubicThetaSeriesTermFDeriv a p n‖≤
      4*Real.pi*‖cubicThetaFrequency n‖*‖cubicThetaSeriesTerm a p.1 p.2 n‖+
        ‖cubicThetaSeriesTermVertical a p.1 p.2 n‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  rw [cubicThetaSeriesTermFDeriv_apply]
  calc
    _ ≤ ‖(tracePair (cubicThetaFrequency n) q.1:ℂ)*
          (2*Real.pi*Complex.I*cubicThetaSeriesTerm a p.1 p.2 n)‖+
        ‖(q.2:ℂ)*cubicThetaSeriesTermVertical a p.1 p.2 n‖ := norm_add_le _ _
    _ = |tracePair (cubicThetaFrequency n) q.1| *
          (2*Real.pi*‖cubicThetaSeriesTerm a p.1 p.2 n‖)+
        ‖q.2‖*‖cubicThetaSeriesTermVertical a p.1 p.2 n‖ := by
      simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    _ ≤ (2*‖cubicThetaFrequency n‖*‖q.1‖)*
          (2*Real.pi*‖cubicThetaSeriesTerm a p.1 p.2 n‖)+
        ‖q.2‖*‖cubicThetaSeriesTermVertical a p.1 p.2 n‖ := by
      gcongr
      exact cubicTheta_tracePair_abs _ _
    _ ≤ (2*‖cubicThetaFrequency n‖*‖q‖)*
          (2*Real.pi*‖cubicThetaSeriesTerm a p.1 p.2 n‖)+
        ‖q‖*‖cubicThetaSeriesTermVertical a p.1 p.2 n‖ := by
      gcongr
      · exact norm_fst_le q
      · exact norm_snd_le q
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
