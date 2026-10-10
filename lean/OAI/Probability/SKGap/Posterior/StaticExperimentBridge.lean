import Mathlib
import OAI.Probability.SKGap.Localization.FixedTimeQuenched
import OAI.Probability.SKGap.Entropy.DisorderWeightedMean
import OAI.Probability.SKGap.Brownian.GibbsContinuity
import OAI.Probability.SKGap.Posterior.ChannelTranslation
import OAI.Probability.SKGap.Brownian.ContinuousPosteriorMass
import OAI.Probability.SKGap.Gaussian.GaussianMarginal
import OAI.Probability.SKGap.Posterior.QuenchedPosterior

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology BigOperators ENNReal
open GaussianStep SKGapCutoff.Recipe SKGapCutoff.Static
noncomputable section
variable {n : ℕ}

lemma halfDiff_sq (f : Spin n→ℝ) (x : Spin n) (i : Fin n) :
    (SKGapCutoff.halfDiff i f x)^2=(f x-f (SKGap.flip i x))^2/4 := by
  rw [SKGapCutoff.halfDiff_as_flip,div_pow,mul_pow,SKGapCutoff.spin_sq]
  norm_num
  rfl

lemma conditionalVariance_eq (p : Prior n) (x : Spin n) (i : Fin n)
    (hp : ∀x,0<p x) :
    conditionalVariance p.mass x i=4*p x*p (SKGap.flip i x)/(p x+p (SKGap.flip i x))^2 := by
  unfold conditionalVariance conditionalMean
  rw [mul_pow,SKGapCutoff.spin_sq,one_mul]
  change 1-((p x-p (SKGap.flip i x))/(p x+p (SKGap.flip i x)))^2=_
  field_simp [(add_pos (hp x) (hp (SKGap.flip i x))).ne']
  ring

lemma varianceEnergy_eq (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ) :
    varianceEnergy p.mass f=energy p f := by
  simp only [varianceEnergy,Finset.mul_sum,energy]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change avg p (fun x=>conditionalVariance p.mass x i*(SKGapCutoff.halfDiff i f x)^2)=_
  rw [avg_flip p i,avg_flip p i]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [conditionalVariance_eq p x i hp,conditionalVariance_eq p (SKGap.flip i x) i hp,
    halfDiff_sq,halfDiff_sq,SKGap.flip_flip,cond_flip]
  unfold GaussianStep.cond
  rw [add_comm (p (SKGap.flip i x)) (p x)]
  field_simp [(add_pos (hp x) (hp (SKGap.flip i x))).ne']
  ring

lemma fieldGibbs_prior (g : Disorder n) (h : Fin n→ℝ) :
    SKGapCutoff.fieldGibbs (coupling g) h=(gibbsPrior g h).mass :=
  SKGapCutoff.fieldGibbs_edge g h

lemma covariance_square_bound {j Aroot ε c r₀ D : ℝ} {g : Disorder n}
    (hD : 0≤D) (H : PosteriorCovarianceProperty j Aroot ε c r₀ D g)
    (h : Fin n→ℝ) (hb : ¬rootBad j Aroot ε c r₀ (coupling g) h) (f : Spin n→ℝ) :
    (∑i,(∑x,gibbsPrior g h x*(f x-avg (gibbsPrior g h) f)*spinValue (x i))^2)≤
      D^2*(var (gibbsPrior g h) f+energy (gibbsPrior g h) f) := by
  have hh:=H h hb f
  rw [fieldGibbs_prior,varianceEnergy_eq _ (mass_pos g h)] at hh
  change SKGapCutoff.Recipe.vectorNorm (centeredSpinCovariance (gibbsPrior g h).mass f) ≤
    D*sqrt (var (gibbsPrior g h) f+energy (gibbsPrior g h) f) at hh
  have hs:=(sq_le_sq₀ (SKGapCutoff.Recipe.vectorNorm_nonneg _)
    (mul_nonneg hD (Real.sqrt_nonneg _))).2 hh
  rw [mul_pow,Real.sq_sqrt (add_nonneg (GaussianStep.var_nonneg _ _) (energy_nonneg _ _)),
    SKGapCutoff.Recipe.vectorNorm_sq] at hs
  exact hs

lemma squareMean_eq (p : Prior n) (f : Spin n→ℝ) (hf : 0<avg p (fun x=>(f x)^2)) :
    squareMean p.mass f=mean (squarePrior p f hf) := rfl

lemma squareMean_one (p : Prior n) : squareMean p.mass (fun _=>1)=mean p := by
  ext i
  simp only [squareMean,squareMass,one_pow,mul_one,p.sum_one,div_one,mean]
  rfl

lemma energy_one (p : Prior n) (hp : ∀x,0<p x) : energy p (fun _=>1)=0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro x _
  have hh : GaussianStep.cond p i (fun _=>1) x=1 := by
    simp [GaussianStep.cond,div_self (add_pos (hp x) (hp (SKGap.flip i x))).ne']
  simp only [hh,sub_self,zero_pow (by decide : 2≠0),mul_zero]

lemma stable_mean_difference {j Aroot ε c r₀ ρ C₀ C : ℝ} {g : Disorder n}
    (hn : 0<n) (hAroot : 1≤Aroot)
    (H : StableSquareMeanProperty j c r₀ ρ C₀ C (coupling g))
    (h : Fin n→ℝ) (hb : ¬rootBad j Aroot ε c r₀ (coupling g) h)
    (f : Spin n→ℝ) (hf : 0<avg (gibbsPrior g h) (fun x=>(f x)^2)) :
    SKGapCutoff.Recipe.vectorNorm (mean (squarePrior (gibbsPrior g h) f hf)-mean (gibbsPrior g h))≤
      2*C₀*ρ*sqrt (n:ℝ)+C*(2+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)) := by
  obtain ⟨r,hr,hu,hall⟩:=stableSquareMeanProperty_rootBad hAroot (coupling g) H h hb
  rw [fieldGibbs_prior] at hall
  have h1:=hall f hf
  have h0:=hall (fun _=>1) (by simp only [one_pow,mul_one,(gibbsPrior g h).sum_one];norm_num)
  rw [varianceEnergy_eq _ (mass_pos g h),squareMean_eq _ _ hf] at h1
  rw [varianceEnergy_eq _ (mass_pos g h),energy_one _ (mass_pos g h),squareMean_one] at h0
  have hs : 0<sqrt (n:ℝ):=sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have h1':= (div_le_iff₀ hs).mp h1
  have h0':= (div_le_iff₀ hs).mp h0
  have hh:=SKGapCutoff.Recipe.vectorNorm_sub
    (mean (squarePrior (gibbsPrior g h) f hf)-magnetization r)
    (mean (gibbsPrior g h)-magnetization r)
  rw [sub_sub_sub_cancel_right] at hh
  apply hh.trans
  calc
    _≤(C₀*ρ+C/sqrt (n:ℝ)*(1+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)))*sqrt (n:ℝ)+
      (C₀*ρ+C/sqrt (n:ℝ)*(1+0/(∑x,gibbsPrior g h x*(1:ℝ)^2)))*sqrt (n:ℝ) := add_le_add h1' h0'
    _=_ := by field_simp;ring

lemma drift_square_of_stable_mean {j Aroot ε c r₀ ρ C₀ C : ℝ} {g : Disorder n}
    (hn : 0<n) (hAroot : 1≤Aroot)
    (H : StableSquareMeanProperty j c r₀ ρ C₀ C (coupling g))
    (h : Fin n→ℝ) (hb : ¬rootBad j Aroot ε c r₀ (coupling g) h)
    (f : Spin n→ℝ) (hf : 0<avg (gibbsPrior g h) (fun x=>(f x)^2)) :
    (∑i,(mean (squarePrior (gibbsPrior g h) f hf) i-mean (gibbsPrior g h) i)^2)≤
      (4*C₀*ρ)*(n:ℝ)+(2*C)*sqrt (n:ℝ)*(2+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)) := by
  let v:=mean (squarePrior (gibbsPrior g h) f hf)-mean (gibbsPrior g h)
  have hm:=stable_mean_difference hn hAroot H h hb f hf
  have hu : SKGapCutoff.Recipe.vectorNorm v≤2*sqrt (n:ℝ) := by
    apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
    simp only [←sq]
    rw [SKGapCutoff.Recipe.vectorNorm_sq,mul_pow,sq_sqrt (Nat.cast_nonneg n)]
    simpa only [v,Pi.sub_apply,show (2:ℝ)^2=4 by norm_num] using
      GaussianHistory.mean_difference_square_le (gibbsPrior g h) (squarePrior (gibbsPrior g h) f hf)
  have hh:=mul_le_mul hm hu (SKGapCutoff.Recipe.vectorNorm_nonneg v) ((SKGapCutoff.Recipe.vectorNorm_nonneg v).trans hm)
  have he : (2*C₀*ρ*sqrt (n:ℝ)+C*(2+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)))*(2*sqrt (n:ℝ))=
      (4*C₀*ρ)*(n:ℝ)+(2*C)*sqrt (n:ℝ)*(2+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)) := by
    calc
      _=(4*C₀*ρ)*(sqrt (n:ℝ))^2+(2*C)*sqrt (n:ℝ)*(2+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)) := by ring
      _=_ := by rw [sq_sqrt (Nat.cast_nonneg n)]
  rw [←sq,SKGapCutoff.Recipe.vectorNorm_sq,he] at hh
  exact hh

end
end SKGap.FullMain

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology BigOperators ENNReal
open GaussianStep GaussianHistory ObservationBridge
noncomputable section
variable {n : ℕ}
local instance : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
local instance : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma gaussianChannelLaw_step (g : Disorder n) (t : ℝ) :
    gaussianChannelLaw g t=(GaussianStep.reference n).withDensity
      (fun z=>ENNReal.ofReal (GaussianStep.density (gibbsPrior g 0) t z)) := by
  have hd : gaussianChannelDensity g t=fun z=>GaussianStep.density (gibbsPrior g 0) t z := by
    funext z
    apply Finset.sum_congr rfl
    intro x _
    change mass g 0 x*exp ((∑i,sqrt t*spinValue (x i)*z i)-(n:ℝ)*t/2)=
      mass g 0 x*exp (sqrt t*(∑i,spinValue (x i)*z i)-t*(n:ℝ)/2)
    congr 2
    simp only [Finset.mul_sum,←mul_assoc,mul_comm (n:ℝ) t]
  change (GaussianStep.reference n).withDensity (fun z=>ENNReal.ofReal (gaussianChannelDensity g t z))=_
  rw [hd]

lemma history_field_event (g : Disorder n) {t : ℝ} (ht : 0≤t) (k : ℕ)
    (E : Set (Fin n→ℝ)) (hE : MeasurableSet E) :
    eventProbability (gibbsPrior g 0) t ((GaussianHistory.field t) ⁻¹' E : Set (History n k))=
      (gaussianChannelLaw g ((k:ℝ)*t)).real
        ((fun z : Fin n→ℝ=>fun i=>sqrt ((k:ℝ)*t)*z i) ⁻¹' E) := by
  have hh:=eventProbability_eq (gibbsPrior g 0) t
    ((GaussianHistory.field t) ⁻¹' E : Set (History n k))
    (hE.preimage (continuous_field t k).measurable)
  rw [←Measure.map_apply (continuous_field t k).measurable hE,
    field_law _ ht k,←gaussianChannelLaw_step,
    Measure.map_apply (by fun_prop) hE] at hh
  simpa only [ENNReal.toReal_ofReal (eventProbability_nonneg _ _ _),Measure.real] using
    congrArg ENNReal.toReal hh

lemma measurable_rootFields (g : Disorder n) (j A ε c ρ : ℝ) :
    MeasurableSet {h:Fin n→ℝ | rootBad j A ε c ρ (coupling g) h} := by
  have hm : Measurable (fun h => (coupling g,h) : Field n → Matrix (Fin n) (Fin n) ℝ × Field n) :=
    measurable_const.prodMk measurable_id
  change MeasurableSet ((fun h => (coupling g,h) : Field n → Matrix (Fin n) (Fin n) ℝ × Field n) ⁻¹'
    {p : Matrix (Fin n) (Fin n) ℝ × Field n | rootBad j A ε c ρ p.1 p.2})
  exact (measurableSet_rootBad (n:=n) j A ε c ρ).preimage hm

lemma history_root_probability (g : Disorder n) {t : ℝ} (ht : 0≤t) (k : ℕ)
    (j A K ε c ρ : ℝ) (hop : operatorBound K (coupling g)) :
    eventProbability (gibbsPrior g 0) t
      {h:History n k | rootBad j A ε c ρ (coupling g) (GaussianHistory.field t h)}=
      fixedTimeFailure n j A K ε c ρ ((k:ℝ)*t) g := by
  let T:=(k:ℝ)*t
  have hT : 0≤T:=mul_nonneg (Nat.cast_nonneg k) ht
  let E:Set (Fin n→ℝ):={h | rootBad j A ε c ρ (coupling g) h}
  have hE : MeasurableSet E:=measurable_rootFields g j A ε c ρ
  change eventProbability (gibbsPrior g 0) t ((GaussianHistory.field t) ⁻¹' E : Set (History n k))=_
  rw [history_field_event g ht k E hE,Measure.real,gaussianChannel_event _ hT _
    (hE.preimage (by fun_prop))]
  change (∑x,ENNReal.ofReal (mass g 0 x)*_).toReal=(fixedTimeFailureENN j A K ε c ρ T g).toReal
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  unfold conditionalSpinFailure
  have hGB : MeasurableSet ((Prod.mk g) ⁻¹' gibbsObservationBad j A K ε c ρ T x) :=
    (measurableSet_gibbsObservationBad j A K ε c ρ T x).preimage
      (show Measurable (Prod.mk g : Field n→Disorder n × Field n) from measurable_const.prodMk measurable_id)
  rw [←GaussianHistory.map_scaled_reference hT,Measure.map_apply (by fun_prop) hGB]
  congr 1
  ext z
  change rootBad j A ε c ρ (coupling g) (fun i=>sqrt T*(z i+sqrt T*spinValue (x i))) ↔
    operatorBound K (coupling g) ∧ rootBad j A ε c ρ (coupling g) (fun i=>T*spinValue (x i)+sqrt T*z i)
  have he : (fun i=>sqrt T*(z i+sqrt T*spinValue (x i)))=(fun i=>T*spinValue (x i)+sqrt T*z i) := by
    funext i
    calc
      _=(sqrt T)^2*spinValue (x i)+sqrt T*z i:=by ring
      _=_:=by rw [sq_sqrt hT]
  rw [he]
  simp only [hop,true_and]

lemma history_terminal_probability (g : Disorder n) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    eventProbability (gibbsPrior g 0) t
      {h:History n k | ¬∀f:Spin n→ℝ,
        variance g (GaussianHistory.field t h) f≤2*dirichlet g (GaussianHistory.field t h) f}=
      (gaussianChannelLaw g ((k:ℝ)*t)).real
        {z | ¬∀f:Spin n→ℝ,variance g (fun i=>sqrt ((k:ℝ)*t)*z i) f≤
          2*dirichlet g (fun i=>sqrt ((k:ℝ)*t)*z i) f} := by
  exact history_field_event g ht k _ (terminal_goodSet_closed g 2).measurableSet.compl

end
end SKGap.FullMain

end OAI
