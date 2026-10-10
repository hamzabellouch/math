import Mathlib
import OAI.Probability.SKGap.Brownian.GramPathRobust
import OAI.Probability.SKGap.Matrix.WordSimultaneousPrediction
import OAI.Probability.SKGap.Stability.WordStablePrediction
import OAI.Probability.SKGap.Stability.QuenchedStableFields
import OAI.Probability.SKGap.Terminal.PairInteraction
import OAI.Probability.SKGap.Entropy.QuenchedFieldAverageExponential
import OAI.Probability.SKGap.Localization.CurieWeiss
import OAI.Probability.SKGap.Gaussian.IndependentBoundedAverageTailLaw
import OAI.Probability.SKGap.Matrix.DoublePlantedGOEArray
import OAI.Probability.SKGap.Localization.DoublePlantedLawTransfer
import OAI.Probability.SKGap.Terminal.PairSpinFrequency
import OAI.Probability.SKGap.Matrix.GapHalfSmallOpNorm
import OAI.Probability.SKGap.Localization.OriginalEventRegeneration
import OAI.Probability.SKGap.Localization.PoissonBinomial
import OAI.Probability.SKGap.Brownian.DiscreteUpperContinuous
import OAI.Probability.SKGap.Brownian.WorstContinuousPolynomialUpper
import OAI.Probability.SKGap.Localization.ScalarSlowConeStep
import OAI.Probability.SKGap.Terminal.SpinDifferenceEnergyReplace
import OAI.Probability.SKGap.Localization.TanhContDiff
import OAI.Probability.SKGap.Localization.JumpBilinear
import OAI.Probability.SKGap.Matrix.StaticCovarianceMatrix
import OAI.Probability.SKGap.Localization.Prediction
import OAI.Probability.SKGap.Matrix.RecipeNodeTrace
import OAI.Probability.SKGap.Matrix.StartedNodeTrace
import OAI.Probability.SKGap.Stability.LocalStartedImplicit
import OAI.Probability.SKGap.Localization.StartedSmall
import OAI.Probability.SKGap.Terminal.TerminalChannel
import OAI.Probability.SKGap.Localization.ModelLocalization

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology BigOperators ENNReal
open GaussianStep GaussianHistory ObservationBridge SKGapCutoff.Recipe SKGapCutoff.Static
noncomputable section

lemma whp_of_measurable_full {β : ℝ} (Ω : ∀n,Set (Disorder n))
    (hΩ : ∀n,MeasurableSet (Ω n))
    (hfull : Tendsto (fun n=>(disorderLaw β n).real (Ω n)) atTop (𝓝 1)) :
    Whp β (fun n g=>g∈Ω n) := by
  apply (whp_iff_real _ _).mpr
  have H:=(tendsto_const_nhds (x:=(1:ℝ))).sub hfull
  simpa only [sub_self,show ∀n,{g:Disorder n | ¬g∈Ω n}=(Ω n)ᶜ from fun _=>rfl,
    probReal_compl_eq_one_sub (hΩ _)] using H

lemma weighted_accuracy {B C₀ r W : ℝ} (hB : 0≤B) (hC₀ : 0≤C₀) (hr : 0<r) (hW : 0<W) :
    ∃ρ:ℝ,0<ρ ∧ B*ρ<r ∧ 4*C₀*ρ≤W := by
  let ρ:=min (r/(2*(B+1))) (W/(2*(4*C₀+1)))
  have hρ : 0<ρ:=lt_min (by positivity) (by positivity)
  have hleft0 : ρ ≤ r/(2*(B+1)) := min_le_left _ _
  have hleft := (le_div_iff₀ (show 0 < 2*(B+1) by positivity)).mp hleft0
  have hright0 : ρ ≤ W/(2*(4*C₀+1)) := min_le_right _ _
  have hright := (le_div_iff₀ (show 0 < 2*(4*C₀+1) by positivity)).mp hright0
  refine ⟨ρ,hρ,?_,?_⟩
  · nlinarith [mul_nonneg hB hρ.le]
  · nlinarith [mul_nonneg hC₀ hρ.le]

lemma exponential_pair_eventually {a d : ℝ} (ha : 0<a) (hd : 0<d) :
    ∀ᶠ n:ℕ in atTop,exp (-a*(n:ℝ))+exp (-d*(n:ℝ))≤exp (-(min a d/2)*(n:ℝ)) := by
  have hm : 0 < min a d := lt_min ha hd
  filter_upwards [constant_exp_absorb 2 hm] with n hn
  calc
    _≤exp (-(min a d)*(n:ℝ))+exp (-(min a d)*(n:ℝ)) :=
      add_le_add (exp_le_exp.mpr (by
        have H := mul_le_mul_of_nonneg_right (min_le_left a d) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
        nlinarith))
        (exp_le_exp.mpr (by
          have H := mul_le_mul_of_nonneg_right (min_le_right a d) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
          nlinarith))
    _=2*exp (-(min a d)*(n:ℝ)):=by ring
    _≤_:=hn

theorem quenched_poincare {β : ℝ} (hβ : 0<β) (hβ1 : β<1) :
    ∃C:ℝ,0<C ∧ Whp β (fun n g=>∀f:Spin n→ℝ,variance g 0 f≤C*dirichlet g 0 f) := by
  obtain ⟨T,aT,hT,haT,Ω,hΩ,hΩfull,hterminal⟩:=terminal_gap_high_probability hβ
  obtain ⟨Ar,K,ε,c,r₀,a,hAr,hK,hs,hε,hc,hr₀,ha,hroot⟩:=quenched_grid_root_stability hβ hβ1 hT
  obtain ⟨D₀,hD₀,hcov⟩:=quenched_posterior_covariance hβ hβ1 hAr hs hε hc hr₀
  let b:=min a aT/2
  have hb : 0<b:=half_pos (lt_min ha haT)
  obtain ⟨W,hW,hnum⟩:=localization_numeric_choice (D₀^2) 2 T a b hT hb
  let P:=physicalNormBound (β^2)
  let C₀:=(1+(P+3*β^2)/c)*(P+4*β^2)
  have hP : 0≤P:=(physicalNormBound_pos (β^2)).le
  have hC₀ : 0≤C₀:=by dsimp [C₀]; positivity
  obtain ⟨ρ,hρ,hbuffer,hlead⟩:=weighted_accuracy (B:=P+4*β^2) (by positivity) hC₀ hr₀ hW
  obtain ⟨Cmean,hCmean,hmean⟩:=disorder_stable_square_mean hβ hβ1 hc hr₀ ρ hρ hbuffer
  let C:=2*(D₀^2*T+3)/exp (-2*D₀^2*T)
  have hC : 0<C:=by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  have hevents:=(((whp_of_measurable_full Ω hΩ hΩfull).and hroot).and hcov).and
    (show Whp β (fun n g=>StableSquareMeanProperty (β^2) c r₀ ρ C₀ Cmean (coupling g)) from hmean)
  apply hevents.mono
  filter_upwards [hnum (2*Cmean),exponential_pair_eventually ha haT] with n hn hr
  intro g hg
  rcases hg with ⟨⟨⟨hgΩ,hgr⟩,hgc⟩,hgm⟩
  rcases hn with ⟨hn,hmesh,hmeshD,hloss,hcost⟩
  have hcost' : localizationCost n (2*Cmean) a b (D₀^2) 2 T≤D₀^2*T+3 := by
    convert hcost using 1; ring
  exact poincare_from_model_data g hn (β^2) Ar K ε c r₀ ρ C₀ Cmean D₀ W a aT b T
    hAr.le hD₀ hW.le hCmean ha hb hT hlead hgr.1 hgr.2 (hterminal n g hgΩ) hgc hgm hr
    hmesh hmeshD hloss hcost'

end
end SKGap.FullMain

namespace SKGap
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology

theorem sk_main (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) : MainStatement β := by
  obtain ⟨C,hC,hwhp⟩:=FullMain.quenched_poincare hβ0 hβ1
  have hP : Tendsto (fun n:ℕ=>disorderLaw β n (poincareEvent n C)) atTop (𝓝 1):=
    FullMain.whp_full_probability hwhp
  exact ⟨C,hC,hP,gap_probability_of_poincare β C hC hP⟩

end SKGap

end OAI
