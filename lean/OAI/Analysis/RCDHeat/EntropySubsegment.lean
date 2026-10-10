import Mathlib
import OAI.Analysis.RCDHeat.EVIConvexity

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: EntropySubsegment, EntropySlopeBound, EntropyPlanLipschitz, EntropyDisjointMixture, EntropyFork. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.entropy_plan_subsegment_bound
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    (C : ℝ≥0) (hc : ∀ s : Time,
      plan.map (fun γ => γ s) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) (R : ℝ) (hs : ∀ s : Time, ∀ᵐ x ∂plan.map (fun γ => γ s), dist x p ≤ R)
    (a b t : Time) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ t)) ≤
      ((b:ℝ)-(t:ℝ))/((b:ℝ)-(a:ℝ))*
        boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ a))+
      ((t:ℝ)-(a:ℝ))/((b:ℝ)-(a:ℝ))*
        boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ b))-
      (K/2)*((t:ℝ)-(a:ℝ))*((b:ℝ)-(t:ℝ))*
        (wassersteinSq (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))).toReal := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let : Nonempty X := ⟨p⟩
  let ν := fun s : Time => plan.map (fun γ => γ s)
  have hpν (s : Time) : IsProbabilityMeasure (ν s) :=
    inferInstance
  let := hpν a
  let := hpν b
  let := hpν t
  have hab' : 0 < (b:ℝ)-(a:ℝ) := sub_pos.mpr hab
  have hat' : 0 ≤ (t:ℝ)-(a:ℝ) := sub_nonneg.mpr hat
  have htb' : 0 ≤ (b:ℝ)-(t:ℝ) := sub_nonneg.mpr htb
  let θ : Time := ⟨((t:ℝ)-(a:ℝ))/((b:ℝ)-(a:ℝ)),
    div_nonneg hat' hab'.le, (div_le_one hab').mpr (by linarith)⟩
  have hθ : 1-(θ:ℝ) = ((b:ℝ)-(t:ℝ))/((b:ℝ)-(a:ℝ)) := by
    dsimp [θ]; field_simp; ring
  have hcost : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞ := by
    rw [← wassersteinSq_eq_cost hp]
    exact wassersteinSq_finite (finiteSecondMoment_of_ae_dist_le _ p (hs 0))
      (finiteSecondMoment_of_ae_dist_le _ p (hs 1))
  have hd (u v : Time) := wassersteinEDist_geodesic_plan plan hg hp hcost u v
  have hdab : wassersteinEDist (ν a) (ν b) =
      ENNReal.ofReal ((b:ℝ)-(a:ℝ))*wassersteinEDist (ν 0) (ν 1) := by
    simpa only [abs_sub_comm (a:ℝ), abs_of_nonneg hab'.le] using hd a b
  have hdta : wassersteinEDist (ν t) (ν a) =
      ENNReal.ofReal (θ:ℝ)*wassersteinEDist (ν a) (ν b) := by
    rw [hdab,←mul_assoc,←ENNReal.ofReal_mul θ.2.1]
    have he : (θ:ℝ)*((b:ℝ)-(a:ℝ)) = (t:ℝ)-(a:ℝ) := by
      dsimp [θ]; field_simp
    rw [he]
    simpa only [abs_of_nonneg hat'] using hd t a
  have hdtb : wassersteinEDist (ν t) (ν b) =
      ENNReal.ofReal (1-(θ:ℝ))*wassersteinEDist (ν a) (ν b) := by
    rw [hdab,←mul_assoc,←ENNReal.ofReal_mul (sub_nonneg.mpr θ.2.2),hθ]
    rw [div_mul_cancel₀ _ hab'.ne']
    simpa only [abs_sub_comm (t:ℝ),abs_of_nonneg htb'] using hd t b
  have hsquare (u v : Measure X) :
      (wassersteinEDist u v).toReal^2 = (wassersteinSq u v).toReal := by
    rw [wassersteinEDist,←ENNReal.toReal_rpow,←Real.sqrt_eq_rpow,
      Real.sq_sqrt ENNReal.toReal_nonneg]
  have hdreal : (wassersteinSq (ν a) (ν b)).toReal =
      ((b:ℝ)-(a:ℝ))^2*(wassersteinSq (ν 0) (ν 1)).toReal := by
    rw [←hsquare,hdab,ENNReal.toReal_mul,ENNReal.toReal_ofReal hab'.le,mul_pow,hsquare]
  have hh := hX.entropy_convexity_bounded_segment K n hn (ν a) (ν b) (ν t)
    C (hc a) (hc b) (hc t) p R (hs a) (hs b) (hs t) θ hdta hdtb
  rw [hθ,hdreal] at hh
  convert hh using 1
  dsimp only [θ]
  field_simp
  ring

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal

lemma bounded_convex_four_values {F0 Fs Ft F1 A B s t δ : ℝ}
    (hδ : 0 < δ) (hδs : δ ≤ s) (hst : s ≤ t) (htδ : t ≤ 1-δ)
    (h0 : F0 ≤ B) (h1 : F1 ≤ B) (hAs : A ≤ Fs) (hBs : Fs ≤ B) (_ : A ≤ Ft)
    (hup : Ft ≤ ((1-t)/(1-s))*Fs+((t-s)/(1-s))*F1)
    (hlo : Fs ≤ ((t-s)/t)*F0+(s/t)*Ft) :
    |Ft-Fs| ≤ ((B-A)/δ)*(t-s) := by
  have hs : 0 < s := lt_of_lt_of_le hδ hδs
  have ht : 0 < t := hs.trans_le hst
  have hs1 : 0 < 1-s := by linarith
  have hts : 0 ≤ t-s := sub_nonneg.mpr hst
  have hup' := mul_le_mul_of_nonneg_left hup hs1.le
  have hlo' := mul_le_mul_of_nonneg_left hlo ht.le
  have hupeq : (1-s)*(((1-t)/(1-s))*Fs+((t-s)/(1-s))*F1) =
      (1-t)*Fs+(t-s)*F1 := by field_simp [hs1.ne']
  have hloeq : t*(((t-s)/t)*F0+(s/t)*Ft) = (t-s)*F0+s*Ft := by field_simp
  rw [hupeq] at hup'
  rw [hloeq] at hlo'
  have hBA : 0 ≤ B-A := sub_nonneg.mpr (hAs.trans hBs)
  have hbup : (t-s)*(F1-Fs) ≤ (t-s)*(B-A) :=
    mul_le_mul_of_nonneg_left (by linarith) hts
  have hblo : (t-s)*(F0-Fs) ≤ (t-s)*(B-A) :=
    mul_le_mul_of_nonneg_left (by linarith) hts
  have hEup : Ft-Fs ≤ (t-s)*(B-A)/(1-s) := by
    apply (le_div_iff₀ hs1).mpr
    nlinarith only [hup',hbup]
  have hElo : Fs-Ft ≤ (t-s)*(B-A)/s := by
    apply (le_div_iff₀ hs).mpr
    nlinarith only [hlo',hblo]
  have hnum : 0 ≤ (t-s)*(B-A) := mul_nonneg hts hBA
  have hu := div_le_div_of_nonneg_left hnum hδ (show δ ≤ 1-s by linarith)
  have hl := div_le_div_of_nonneg_left hnum hδ hδs
  rw [abs_le]
  constructor
  · have hh := hElo.trans hl
    have he : (t-s)*(B-A)/δ = ((B-A)/δ)*(t-s) := by ring
    rw [he] at hh
    linarith
  · have hh := hEup.trans hu
    convert hh using 1; ring

lemma bounded_semiconvex_four_values {E0 Es Et E1 L U s t δ q : ℝ}
    (hδ : 0 < δ) (hδs : δ ≤ s) (hst : s ≤ t) (htδ : t ≤ 1-δ)
    (h0 : E0 ≤ U) (h1 : E1 ≤ U) (hLs : L ≤ Es) (hUs : Es ≤ U) (hLt : L ≤ Et)
    (hup : Et ≤ ((1-t)/(1-s))*Es+((t-s)/(1-s))*E1-q*(t-s)*(1-t))
    (hlo : Es ≤ ((t-s)/t)*E0+(s/t)*Et-q*s*(t-s)) :
    |Et-Es| ≤ (((U-L+2*|q|)/δ)+2*|q|)*(t-s) := by
  have hs : 0 < s := lt_of_lt_of_le hδ hδs
  have ht : 0 < t := hs.trans_le hst
  have ht1 : t ≤ 1 := by linarith
  have hs1 : s < 1 := by linarith
  have hs_sq : 0 ≤ s^2 ∧ s^2 ≤ 1 := ⟨sq_nonneg s,by nlinarith⟩
  have ht_sq : 0 ≤ t^2 ∧ t^2 ≤ 1 := ⟨sq_nonneg t,by nlinarith⟩
  have hb (v : ℝ) (hv : 0 ≤ v) (hv1 : v ≤ 1) : |q*v| ≤ |q| := by
    rw [abs_mul,abs_of_nonneg hv]
    exact (mul_le_mul_of_nonneg_left hv1 (abs_nonneg q)).trans_eq (mul_one _)
  have hbs := (abs_le.mp (hb _ hs_sq.1 hs_sq.2))
  have hbt := (abs_le.mp (hb _ ht_sq.1 ht_sq.2))
  have heup : Et-q*t^2 ≤ ((1-t)/(1-s))*(Es-q*s^2)+
      ((t-s)/(1-s))*(E1-q) := by
    have he : ((1-t)/(1-s))*(Es-q*s^2)+((t-s)/(1-s))*(E1-q) =
        ((1-t)/(1-s))*Es+((t-s)/(1-s))*E1-q*(t-s)*(1-t)-q*t^2 := by
      field_simp [ne_of_gt (sub_pos.mpr hs1)]; ring
    rw [he]; linarith
  have helo : Es-q*s^2 ≤ ((t-s)/t)*E0+(s/t)*(Et-q*t^2) := by
    have he : ((t-s)/t)*E0+(s/t)*(Et-q*t^2) =
        ((t-s)/t)*E0+(s/t)*Et-q*s*(t-s)-q*s^2 := by
      field_simp [ne_of_gt (sub_pos.mpr hs1)]; ring
    rw [he]; linarith
  have hh := bounded_convex_four_values (A := L-|q|) (B := U+|q|)
    hδ hδs hst htδ (by linarith [abs_nonneg q])
    (by linarith [neg_abs_le q]) (by linarith) (by linarith) (by linarith) heup helo
  have hqr : |q*(t^2-s^2)| ≤ 2*|q| *(t-s) := by
    rw [show t^2-s^2 = (t-s)*(t+s) from by ring,abs_mul,abs_mul,
      abs_of_nonneg (sub_nonneg.mpr hst),abs_of_nonneg (by linarith : 0 ≤ t+s)]
    have hh := mul_le_mul_of_nonneg_left (show t+s ≤ 2 by linarith)
      (mul_nonneg (abs_nonneg q) (sub_nonneg.mpr hst))
    nlinarith only [hh]
  calc
    |Et-Es| = |((Et-q*t^2)-(Es-q*s^2))+q*(t^2-s^2)| := by congr 1; ring
    _ ≤ |(Et-q*t^2)-(Es-q*s^2)|+|q*(t^2-s^2)| := abs_add_le _ _
    _ ≤ ((U+|q|-(L-|q|))/δ)*(t-s)+2*|q| *(t-s) := add_le_add hh hqr
    _ = _ := by ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MetricSpace X] [BorelSpace X] in
theorem entropy_ge_neg_twice_support_volume (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ)
    {S : Set X} (hS : MeasurableSet S) [IsFiniteMeasure (μ.restrict S)]
    (hs : ∀ᵐ x ∂ν, x ∈ S) :
    -2*(μ S).toReal ≤ boltzmannEntropy μ ν := by
  have hloc : ν ≤ C • μ.restrict S := (compression_iff_localized μ ν hs C).mp hν
  have hac := Measure.absolutelyContinuous_of_le_smul hloc
  have hi := entropy_integrable_of_bounded_support μ ν hC hν hS hs
  have hi' := (entropy_integrable_localized_iff μ ν hS hac).mp hi
  rw [boltzmannEntropy_localized μ ν hS hac]
  have hh := integral_mono_ae (integrable_const (-2:ℝ)) hi'
    (Filter.Eventually.of_forall fun x => entropy_density_lower
      (ENNReal.toReal_nonneg (a := ν.rnDeriv (μ.restrict S) x)))
  simpa only [boltzmannEntropy,integral_const,Measure.restrict_apply_univ,
    Measure.real,smul_eq_mul,mul_comm] using hh

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.entropy_compressed_plan_lipschitz
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    {C : ℝ} (hC : 0 < C) (hc : ∀ u : Time,
      plan.map (fun γ => γ u) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) (R : ℝ) (hs : ∀ u : Time, ∀ᵐ x ∂plan.map (fun γ => γ u), dist x p ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (s t : Time) (hδs : δ ≤ (s:ℝ))
    (hst : s ≤ t) (htδ : (t:ℝ) ≤ 1-δ) :
    let q := (K/2)*(wassersteinSq (plan.map (fun γ => γ 0))
      (plan.map (fun γ => γ 1))).toReal
    |boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ t))-
      boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ s))| ≤
      (((Real.log C+2*(hausdorff n X (closedBall p R)).toReal+2*|q|)/δ)+2*|q|)*
        ((t:ℝ)-(s:ℝ)) := by
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsFiniteMeasure (μ.restrict (closedBall p R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall p R).measure_lt_top⟩
  let E := fun u : Time => boltzmannEntropy μ (plan.map (fun γ => γ u))
  have hprob (u : Time) : IsProbabilityMeasure (plan.map (fun γ => γ u)) :=
    inferInstance
  have hupper (u : Time) : E u ≤ Real.log C := by
    let := hprob u
    exact entropy_le_log_density_bound μ _ hC (hc u) measurableSet_closedBall (hs u)
  have hlower (u : Time) : -2*(μ (closedBall p R)).toReal ≤ E u :=
    entropy_ge_neg_twice_support_volume μ _ ENNReal.ofReal_ne_top (hc u)
      measurableSet_closedBall (hs u)
  have hs1 : s < (1:Time) := by change (s:ℝ) < 1; exact lt_of_le_of_lt hst (by linarith)
  have ht0 : (0:Time) < t := by change 0 < (t:ℝ); exact lt_of_lt_of_le (lt_of_lt_of_le hδ hδs) hst
  have hup := hX.entropy_plan_subsegment_bound K n hn plan hg hp ⟨C,hC.le⟩ hc
    p R hs s 1 t hst t.2.2 hs1
  have hlo := hX.entropy_plan_subsegment_bound K n hn plan hg hp ⟨C,hC.le⟩ hc
    p R hs 0 t s s.2.1 hst ht0
  have hh := bounded_semiconvex_four_values
    (q := (K/2)*(wassersteinSq (plan.map (fun γ => γ 0))
      (plan.map (fun γ => γ 1))).toReal)
    hδ hδs hst htδ (hupper 0) (hupper 1) (hlower s) (hupper s) (hlower t)
    (by simpa only [E,μ,show ((1:Time):ℝ)=1 from rfl,mul_assoc,mul_comm,mul_left_comm] using hup)
    (by simpa only [E,μ,show ((0:Time):ℝ)=0 from rfl,sub_zero,
      mul_assoc,mul_comm,mul_left_comm] using hlo)
  simpa only [neg_mul,sub_neg_eq_add,E,μ] using hh

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem entropy_disjoint_probability_midpoint (μ ν₀ ν₁ : Measure X) [SigmaFinite μ]
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (ha0 : ν₀ ≪ μ) (ha1 : ν₁ ≪ μ) (hdis : ν₀ ⟂ₘ ν₁)
    (hi0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (hi1 : Integrable (fun x => (ν₁.rnDeriv μ x).toReal*Real.log (ν₁.rnDeriv μ x).toReal) μ) :
    boltzmannEntropy μ ((1/2:ℝ≥0∞) • (ν₀+ν₁)) =
      (boltzmannEntropy μ ν₀+boltzmannEntropy μ ν₁)/2-Real.log 2 := by
  let η := (1/2:ℝ≥0∞) • (ν₀+ν₁)
  let : IsFiniteMeasure η := ⟨by simp [η,Measure.smul_apply,Measure.add_apply]⟩
  have hr : η.rnDeriv μ =ᵐ[μ] fun x => (1/2:ℝ≥0∞)*(ν₀.rnDeriv μ x+ν₁.rnDeriv μ x) := by
    filter_upwards [Measure.rnDeriv_smul_left_of_ne_top (ν₀+ν₁) μ
      (r := (1/2:ℝ≥0∞)) (by norm_num),Measure.rnDeriv_add ν₀ ν₁ μ] with x hx hy
    simpa only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,hy] using hx
  have hl0 : (fun x => Real.log (η.rnDeriv μ x).toReal) =ᵐ[ν₀]
      (fun x => Real.log (ν₀.rnDeriv μ x).toReal-Real.log 2) := by
    filter_upwards [ha0.ae_le hr,Measure.rnDeriv_eq_zero_of_mutuallySingular hdis.symm ha0,
      Measure.rnDeriv_pos ha0,ha0.ae_le (Measure.rnDeriv_lt_top ν₀ μ)] with x hx hy hz hf
    change ν₁.rnDeriv μ x = 0 at hy
    rw [hx,hy,add_zero,ENNReal.toReal_mul]
    norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
    rw [show (1/(2:ℝ))*(ν₀.rnDeriv μ x).toReal = (ν₀.rnDeriv μ x).toReal/2 from by ring,
      Real.log_div (ENNReal.toReal_pos hz.ne' hf.ne).ne' (by norm_num)]
  have hl1 : (fun x => Real.log (η.rnDeriv μ x).toReal) =ᵐ[ν₁]
      (fun x => Real.log (ν₁.rnDeriv μ x).toReal-Real.log 2) := by
    filter_upwards [ha1.ae_le hr,Measure.rnDeriv_eq_zero_of_mutuallySingular hdis ha1,
      Measure.rnDeriv_pos ha1,ha1.ae_le (Measure.rnDeriv_lt_top ν₁ μ)] with x hx hy hz hf
    change ν₀.rnDeriv μ x = 0 at hy
    rw [hx,hy,zero_add,ENNReal.toReal_mul]
    norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
    rw [show (1/(2:ℝ))*(ν₁.rnDeriv μ x).toReal = (ν₁.rnDeriv μ x).toReal/2 from by ring,
      Real.log_div (ENNReal.toReal_pos hz.ne' hf.ne).ne' (by norm_num)]
  have hil0 := (integrable_toReal_rnDeriv_mul_iff ha0).mp hi0
  have hil1 := (integrable_toReal_rnDeriv_mul_iff ha1).mp hi1
  have hiη0 : Integrable (fun x => Real.log (η.rnDeriv μ x).toReal) ν₀ :=
    (hil0.sub (integrable_const _)).congr hl0.symm
  have hiη1 : Integrable (fun x => Real.log (η.rnDeriv μ x).toReal) ν₁ :=
    (hil1.sub (integrable_const _)).congr hl1.symm
  have haη : η ≪ μ := (ha0.add_left ha1).smul_left _
  have he (ν : Measure X) [IsFiniteMeasure ν] (ha : ν ≪ μ) :
      boltzmannEntropy μ ν = ∫ x, Real.log (ν.rnDeriv μ x).toReal ∂ν :=
    integral_rnDeriv_smul (f := fun x => Real.log (ν.rnDeriv μ x).toReal) ha
  change boltzmannEntropy μ η = _
  rw [he η haη,show η = (1/2:ℝ≥0∞) • (ν₀+ν₁) from rfl,integral_smul_measure,
    integral_add_measure hiη0 hiη1,integral_congr_ae hl0,integral_congr_ae hl1,
    integral_sub hil0 (integrable_const _),integral_sub hil1 (integrable_const _)]
  simp only [integral_const,probReal_univ,ENNReal.toReal_div,
    ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul,←he ν₀ ha0,←he ν₁ ha1]
  ring

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.entropy_compressed_plan_lipschitz_uniform
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))))
    {C : ℝ} (hC : 0 < C) (hc : ∀ u : Time,
      plan.map (fun γ => γ u) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ u : Time, ∀ᵐ x ∂plan.map (fun γ => γ u), dist x p ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (s t : Time) (hδs : δ ≤ (s:ℝ))
    (hst : s ≤ t) (htδ : (t:ℝ) ≤ 1-δ) :
    |boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ t))-
      boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ s))| ≤
      (((Real.log C+2*(hausdorff n X (closedBall p R)).toReal+4*|K| *R^2)/δ)+
        4*|K| *R^2)*((t:ℝ)-(s:ℝ)) := by
  let : IsProbabilityMeasure (plan.map (fun γ => γ 0)) :=
    inferInstance
  let : IsProbabilityMeasure (plan.map (fun γ => γ 1)) :=
    inferInstance
  have hh := hX.entropy_compressed_plan_lipschitz K n hn plan hg hp hC hc p R hs hδ s t hδs hst htδ
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr (show (s:ℝ) ≤ (t:ℝ) from hst))
  let : SeparableSpace X := hX.separable
  have hD := wassersteinSq_ball_bound p p hR (hs 0) (hs 1)
  simp only [dist_self,zero_add] at hD
  have hq : 2*|(K/2)*(wassersteinSq (plan.map (fun γ => γ 0))
      (plan.map (fun γ => γ 1))).toReal| ≤ 4*|K| *R^2 := by
    rw [abs_mul,abs_div,abs_of_nonneg (ENNReal.toReal_nonneg),abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := mul_le_mul_of_nonneg_left hD (abs_nonneg K)
    nlinarith only [hh]
  exact add_le_add (div_le_div_of_nonneg_right (by linarith only [hq]) hδ.le) hq

 

theorem NoncollapsedRCD.entropy_fork_gap
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (P : Fin 3 → Measure C(Time,X)) (hprob : ∀ i, IsProbabilityMeasure (P i))
    (hg : ∀ i, ∀ᵐ γ ∂P i, IsGeodesic γ)
    (hp : ∀ i, IsOptimalCoupling ((P i).map (fun γ => γ 0)) ((P i).map (fun γ => γ 1))
      ((P i).map (fun γ => (γ 0,γ 1))))
    (hmix : P 2 = (1/2:ℝ≥0∞) • (P 0+P 1))
    {C : ℝ} (hC : 0 < C) (hc : ∀ i (u : Time),
      (P i).map (fun γ => γ u) ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ i (u : Time), ∀ᵐ x ∂(P i).map (fun γ => γ u), dist x p ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (s t : Time) (hδs : δ ≤ (s:ℝ))
    (hst : s ≤ t) (htδ : (t:ℝ) ≤ 1-δ)
    (he : (P 0).map (fun γ => γ s) = (P 1).map (fun γ => γ s))
    (hd : (P 0).map (fun γ => γ t) ⟂ₘ (P 1).map (fun γ => γ t)) :
    Real.log 2 ≤ 2*((((Real.log C+2*(hausdorff n X (closedBall p R)).toReal+4*|K| *R^2)/δ)+
        4*|K| *R^2)*((t:ℝ)-(s:ℝ))) := by
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsFiniteMeasure (μ.restrict (closedBall p R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall p R).measure_lt_top⟩
  let ν := fun i (u : Time) => (P i).map (fun γ => γ u)
  have hνprob (i) (u : Time) : IsProbabilityMeasure (ν i u) := by
    let := hprob i
    exact inferInstance
  let E := fun i u => boltzmannEntropy μ (ν i u)
  have hmixν (u : Time) : ν 2 u = (1/2:ℝ≥0∞) • (ν 0 u+ν 1 u) := by
    dsimp only [ν]
    rw [hmix,Measure.map_smul _ (measurable_path_eval u).aemeasurable,
      Measure.map_add _ _ (measurable_path_eval u)]
  change ν 0 s = ν 1 s at he
  have he2 : ν 2 s = ν 0 s := by
    rw [hmixν,←he,←two_smul ℝ≥0∞ _,smul_smul]
    norm_num [ENNReal.inv_mul_cancel]
  have he0 : E 0 s = E 1 s := congrArg (boltzmannEntropy μ) he
  have hem : E 2 s = E 0 s := congrArg (boltzmannEntropy μ) he2
  have hgap : E 2 t = (E 0 t+E 1 t)/2-Real.log 2 := by
    dsimp only [E]
    rw [hmixν]
    let := hνprob 0 t
    let := hνprob 1 t
    exact entropy_disjoint_probability_midpoint μ (ν 0 t) (ν 1 t)
      (Measure.absolutelyContinuous_of_le_smul (hc 0 t))
      (Measure.absolutelyContinuous_of_le_smul (hc 1 t)) hd
      (entropy_integrable_of_bounded_support μ _ ENNReal.ofReal_ne_top (hc 0 t)
        measurableSet_closedBall (hs 0 t))
      (entropy_integrable_of_bounded_support μ _ ENNReal.ofReal_ne_top (hc 1 t)
        measurableSet_closedBall (hs 1 t))
  have hLip i := by
    let := hprob i
    exact hX.entropy_compressed_plan_lipschitz_uniform K n hn (P i) (hg i) (hp i)
      hC (hc i) p hR (hs i) hδ s t hδs hst htδ
  have h0 := (abs_le.mp (hLip 0)).2
  have h1 := (abs_le.mp (hLip 1)).2
  have hm := (abs_le.mp (hLip 2)).1
  change E 0 t-E 0 s ≤ _ at h0
  change E 1 t-E 1 s ≤ _ at h1
  change _ ≤ E 2 t-E 2 s at hm
  linarith only [h0,h1,hm,hgap,he0,hem]


end RegularPointCoordinates

end OAI
