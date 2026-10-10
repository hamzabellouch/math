import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.CentralOccupation

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma selectionWeight_pos {P θ φ h : ℝ} (hP : 0<P) (hθ : 0<θ) (hφ : 0<φ) (hh : 0<h) :
    0<selectionWeight P θ φ h := by unfold selectionWeight; positivity

lemma selectionWeight_log {P θ φ h : ℝ} (hP : 0<P) (hθ : 0<θ) (hφ : 0<φ) (hh : 0<h) :
    Real.log (selectionWeight P θ φ h)=
      (-(Real.log P+Real.log θ)+Real.log φ+Real.log h)/100000 := by
  unfold selectionWeight
  rw [Real.log_mul (mul_ne_zero (Real.rpow_pos_of_pos (mul_pos hP hθ) _).ne'
      (Real.rpow_pos_of_pos hφ _).ne') (Real.rpow_pos_of_pos hh _).ne',
    Real.log_mul (Real.rpow_pos_of_pos (mul_pos hP hθ) _).ne' (Real.rpow_pos_of_pos hφ _).ne',
    Real.log_rpow (mul_pos hP hθ),Real.log_rpow hφ,Real.log_rpow hh,Real.log_mul hP.ne' hθ.ne']
  ring

lemma selected_long_time_weight_scalar {P p θ φ h I μ : ℝ}
    (hP : 0<P) (hp : 0<p) (hpP : p≤P) (hθ : 0<θ) (hφ : 0<φ) (hφ1 : φ≤1)
    (hh : 0<h) (hh1 : h≤1) (hI : 0<I) (hμ : μ≤h/p)
    (hne : P*Real.sqrt I*selectionWeight P θ φ h<I*Real.sqrt h*p^2*φ^2)
    (hfar : P*Real.sqrt I*selectionWeight P θ φ h<
      Real.sqrt I*Real.sqrt (p*μ)/(θ*h)) :
    h^2*p^3*θ^3*φ≤P*Real.sqrt I*selectionWeight P θ φ h := by
  let W := selectionWeight P θ φ h
  have hW : 0<W := selectionWeight_pos hP hθ hφ hh
  have hsI : 0<Real.sqrt I := Real.sqrt_pos.mpr hI
  have hsh : 0<Real.sqrt h := Real.sqrt_pos.mpr hh
  have hroot : Real.sqrt (p*μ)≤Real.sqrt h := Real.sqrt_le_sqrt (by
    calc p*μ≤p*(h/p) := mul_le_mul_of_nonneg_left hμ hp.le
         _=h := by field_simp)
  have hf : P*θ*Real.sqrt h*W<1 := by
    have hf' := (lt_div_iff₀ (mul_pos hθ hh)).mp hfar
    have hf'' : P*W*(θ*h)<Real.sqrt h := by
      apply (mul_lt_mul_iff_right₀ hsI).mp
      calc Real.sqrt I*(P*W*(θ*h))=(P*Real.sqrt I*W)*(θ*h) := by ring
           _<Real.sqrt I*Real.sqrt (p*μ) := hf'
           _≤Real.sqrt I*Real.sqrt h := mul_le_mul_of_nonneg_left hroot hsI.le
    apply (mul_lt_mul_iff_left₀ hsh).mp
    calc
      (P*θ*Real.sqrt h*W)*Real.sqrt h=P*W*θ*(Real.sqrt h*Real.sqrt h) := by ring
      _=P*W*(θ*h) := by rw [Real.mul_self_sqrt hh.le]; ring
      _<1*Real.sqrt h := by simpa only [one_mul] using hf''
  have hfLog := Real.log_lt_log (by positivity : 0<P*θ*Real.sqrt h*W) hf
  rw [Real.log_one,Real.log_mul (by positivity) hW.ne',Real.log_mul (by positivity) hsh.ne',
    Real.log_mul hP.ne' hθ.ne',Real.log_sqrt hh.le] at hfLog
  have hnLog := Real.log_lt_log (by positivity : 0<P*Real.sqrt I*W) hne
  rw [Real.log_mul (by positivity) hW.ne',Real.log_mul hP.ne' hsI.ne',
    Real.log_mul (by positivity) (pow_pos hφ 2).ne',Real.log_mul (by positivity) (pow_pos hp 2).ne',
    Real.log_mul hI.ne' hsh.ne',Real.log_sqrt hh.le,Real.log_sqrt hI.le,
    Real.log_pow,Real.log_pow] at hnLog
  have hlogW := selectionWeight_log hP hθ hφ hh
  have hlh : Real.log h≤0 := Real.log_nonpos hh.le hh1
  have hlφ : Real.log φ≤0 := Real.log_nonpos hφ.le hφ1
  have hlp : Real.log p≤Real.log P := Real.log_le_log hp hpP
  have hlogs : Real.log (h^2*p^3*θ^3*φ)≤Real.log (P*Real.sqrt I*W) := by
    rw [Real.log_mul (by positivity) hφ.ne',Real.log_mul (by positivity) (pow_pos hθ 3).ne',
      Real.log_mul (pow_pos hh 2).ne' (pow_pos hp 3).ne',Real.log_pow,Real.log_pow,Real.log_pow,
      Real.log_mul (by positivity) hW.ne',Real.log_mul hP.ne' hsI.ne',Real.log_sqrt hI.le]
    change Real.log W= _ at hlogW
    norm_num at hnLog ⊢
    linarith
  exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hlogs

lemma selectionWeight_sq {P θ φ h : ℝ} (hP : 0<P) (hθ : 0<θ) (hφ : 0<φ) (hh : 0<h) :
    selectionWeight P θ φ h ^ 2 =
      P^(-(1/50000:ℝ))*θ^(-(1/50000:ℝ))*φ^(1/50000:ℝ)*h^(1/50000:ℝ) := by
  have he {x e : ℝ} (hx : 0<x) : (x^e)^2=x^(e*2) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]
    norm_num
  unfold selectionWeight
  rw [mul_pow,mul_pow,he (mul_pos hP hθ),he hφ,he hh,
    Real.mul_rpow hP.le hθ.le]
  norm_num

def spatialThresholdA (P p φ : ℝ) : ℝ :=
  P^2*P^(-(1/50000:ℝ))*φ^(1/50000:ℝ)/(p*φ)

def spatialThresholdB (P I p φ : ℝ) : ℝ :=
  P^2*P^(-(1/50000:ℝ))*φ^(1/50000:ℝ)/((32768:ℝ)^2*I*p^4*φ^4)

lemma spatialThresholdA_pos {P p φ : ℝ} (hP : 0<P) (hp : 0<p) (hφ : 0<φ) :
    0<spatialThresholdA P p φ := by unfold spatialThresholdA; positivity

lemma spatialThresholdB_pos {P I p φ : ℝ} (hP : 0<P) (hI : 0<I) (hp : 0<p) (hφ : 0<φ) :
    0<spatialThresholdB P I p φ := by unfold spatialThresholdB; positivity

lemma spatial_polynomial_normalisation {P p θ φ h : ℝ}
    (hP : 0<P) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hh : 0<h) :
    P^2*(selectionWeight P θ φ h)^2*θ/(p*φ)=
      spatialThresholdA P p φ*θ^(1-(1/50000:ℝ))*h^(1/50000:ℝ) := by
  rw [selectionWeight_sq hP hθ hφ hh]
  have he : θ^(-(1/50000:ℝ))*θ=θ^(1-(1/50000:ℝ)) := by
    rw [mul_comm]
    calc
      _=θ^(1:ℝ)*θ^(-(1/50000:ℝ)) := by rw [Real.rpow_one]
      _=_ := by rw [←Real.rpow_add hθ]; norm_num
  unfold spatialThresholdA
  calc
    _=(P^2*P^(-(1/50000:ℝ))*φ^(1/50000:ℝ)/(p*φ))*
       (θ^(-(1/50000:ℝ))*θ)*h^(1/50000:ℝ) := by
         apply (div_eq_iff (mul_pos hp hφ).ne').mpr
         field_simp
    _=_ := by rw [he]

lemma near_lower_radial_condition {P I p θ φ h : ℝ}
    (hP : 0<P) (hI : 0<I) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hh : 0<h)
    (hnear : P*Real.sqrt I*selectionWeight P θ φ h <
      32768*(I*Real.sqrt h*p^2*φ^2)) :
    spatialThresholdB P I p φ*θ^(-(1/50000:ℝ))≤h^(1-(1/50000:ℝ)) := by
  have hWpos := selectionWeight_pos hP hθ hφ hh
  have hs := pow_le_pow_left₀ (by positivity : 0≤P*Real.sqrt I*selectionWeight P θ φ h) hnear.le 2
  have hW := selectionWeight_sq hP hθ hφ hh
  have hr : h^(1-(1/50000:ℝ))*h^(1/50000:ℝ)=h := by
    rw [←Real.rpow_add hh]
    norm_num
  let B := (32768:ℝ)^2*(I:ℝ)^2*p^4*φ^4*h^(1/50000:ℝ)
  have hB : 0<B := by dsimp [B]; positivity
  apply (mul_le_mul_iff_right₀ hB).mp
  calc
    _=(P*Real.sqrt I*selectionWeight P θ φ h)^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt hI.le,hW]
      dsimp [spatialThresholdB,B]
      field_simp
    _≤(32768*(I*Real.sqrt h*p^2*φ^2))^2 := hs
    _=B*h^(1-(1/50000:ℝ)) := by
      rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hh.le]
      dsimp [B]
      calc
        _=(32768:ℝ)^2*(I:ℝ)^2*p^4*φ^4*h := by ring
        _=(32768:ℝ)^2*(I:ℝ)^2*p^4*φ^4*(h^(1-(1/50000:ℝ))*h^(1/50000:ℝ)) := by rw [hr]
        _=_ := by ring

lemma selected_neighbor_radial_condition {P M A w I : ℝ} (hP : 0<P) (hI : 0<I)
    {j k : Fin 4→ℕ} (hj : representativeSelected P M A w I j)
    (hjk : ∀i,j i≤k i+2 ∧ k i≤j i+2) :
    spatialThresholdB P I (sourceRepresentative (k 0)) (cappedRepresentative (k 2))*
      (cappedRepresentative (k 1))^(-(1/50000:ℝ))≤
        (cappedRepresentative (k 3))^(1-(1/50000:ℝ)) := by
  exact near_lower_radial_condition hP hI (by dsimp [sourceRepresentative]; positivity)
    (cappedRepresentative_pos _) (cappedRepresentative_pos _) (cappedRepresentative_pos _)
    (selected_neighbor_near_lower hP hI hj hjk)

lemma spatial_crossing_datum_scale {P I p φ R : ℝ}
    (hP : 0<P) (hI : 0<I) (hp : 0<p) (hφ : 0<φ) (hR : 0≤R) :
    Real.sqrt (spatialThresholdA P p φ*(R^2/(p*φ))/spatialThresholdB P I p φ)=
      32768*Real.sqrt I*R*p*φ := by
  have he : spatialThresholdA P p φ*(R^2/(p*φ))/spatialThresholdB P I p φ=
      (32768*R*p*φ)^2*I := by
    unfold spatialThresholdA spatialThresholdB
    field_simp
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
  ring

lemma tsum_quad_pair_index (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,f k)=∑'n : ℕ×ℕ,∑'nt : ℕ,∑'nr : ℕ,f ![n.1,nt,n.2,nr] := by
  rw [tsum_quad_index,ENNReal.tsum_prod']
  apply tsum_congr
  intro np
  exact ENNReal.tsum_comm

def centralIndexSector (P : ℝ) : Set (Fin 4→ℕ) :=
  {k | sourceRepresentative (k 0)≤P ∧
    1/sourceRepresentative (k 0)≤cappedRepresentative (k 2) ∧
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16}

lemma tsum_centralIndexSector (P : ℝ) (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,(centralIndexSector P).indicator f k)=
      ∑'n : ℕ×ℕ,({n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}).indicator
        (fun n=>∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤cappedRepresentative n.2/16
          then f ![n.1,nt,n.2,nr] else 0) n := by
  classical
  rw [tsum_quad_pair_index]
  apply tsum_congr
  intro n
  by_cases hn : sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1≤cappedRepresentative n.2
  · have hn' : n∈{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2} := hn
    rw [indicator_of_mem hn']
    apply tsum_congr
    intro nt
    apply tsum_congr
    intro nr
    have hi : (![n.1,nt,n.2,nr]∈centralIndexSector P) ↔
        cappedRepresentative nt≤cappedRepresentative n.2/16 := by
      change (sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2 ∧
        cappedRepresentative nt≤cappedRepresentative n.2/16) ↔_
      simp only [hn.1,hn.2,true_and]
    simp only [indicator_apply,hi]
  · have hn' : n∉{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2} := hn
    rw [indicator_of_notMem hn']
    apply ENNReal.tsum_eq_zero.mpr
    intro nt
    apply ENNReal.tsum_eq_zero.mpr
    intro nr
    apply indicator_of_notMem
    change ¬(sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2 ∧
      cappedRepresentative nt≤cappedRepresentative n.2/16)
    exact fun h=>hn ⟨h.1,h.2.1⟩

lemma representativeSmallSector_subset_centralIndexSector (P : ℝ) :
    representativeSmallSector P⊆centralIndexSector P := by
  intro k hk
  refine ⟨hk.1,hk.2.1.trans (hk.2.2.trans ?_),hk.2.2⟩
  have hφ := (cappedRepresentative_pos (k 2)).le
  linarith



section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma representativeSpatialCost_le_central_structural {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ)
    (hangle : cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1)) :
    representativeSpatialCost s F zX w k a b≤
      ENNReal.ofReal 16384*representativeCentralCost s F zX w k a b := by
  unfold representativeSpatialCost
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (cappedRepresentative_pos _)).mpr
  linarith

lemma Admissible.spatial_structural_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 1≤w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {k | k∈centralIndexSector P ∧
        cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1)}
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>representativeSpatialCost s F zX w k a b) k)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cc,hCc,hcentral⟩ := hd.central_uniform T₀
  refine ⟨16384*Cc,by positivity,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
  dsimp only
  let Q := {k | k∈centralIndexSector P ∧
    cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1)}
  let fc := fun k=>representativeCentralCost s F zX w k a b
  let fs := fun k=>representativeSpatialCost s F zX w k a b
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hpoint (k : Fin 4→ℕ) : Q.indicator fs k≤
      ENNReal.ofReal 16384*(centralIndexSector P).indicator fc k := by
    by_cases hk : k∈Q
    · rw [indicator_of_mem hk,indicator_of_mem hk.1]
      exact representativeSpatialCost_le_central_structural F zX w k a b hk.2
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hc := hcentral M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
  dsimp only at hc
  rw [←tsum_centralIndexSector P (fun k=>representativeCentralCost s F zX w k a b)] at hc
  change (∑'k,Q.indicator fs k)≤ENNReal.ofReal ((16384*Cc)*B)
  calc
    _≤∑'k,ENNReal.ofReal 16384*(centralIndexSector P).indicator fc k := ENNReal.tsum_le_tsum hpoint
    _=ENNReal.ofReal 16384*(∑'k,(centralIndexSector P).indicator fc k) := ENNReal.tsum_mul_left
    _≤ENNReal.ofReal 16384*ENNReal.ofReal (Cc*B) := mul_le_mul' le_rfl hc
    _=_ := by rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤16384)]; congr 1; ring


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma EnergyPrefix.particleCone_lintegral {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) (n : Sphere) :
    (∫⁻v : Vec,ENNReal.ofReal (q v*(1-dot n.1 (velocity v))*s.f (t,(x,v))))=
      ENNReal.ofReal (particleEnergy s (t,x)-dot n.1 (particleFlux s (t,x))) := by
  obtain ⟨hf,hc⟩ := hs.velocity_slice ht x
  have hi : Integrable (fun v : Vec=>q v*(1-dot n.1 (velocity v))*s.f (t,(x,v))) :=
    (((contDiff_q (k:=0)).continuous.mul (continuous_const.sub
      (continuous_dot.comp (continuous_const.prodMk (contDiff_velocity (k:=0)).continuous)))).mul
      hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun v=>
    mul_nonneg (mul_nonneg (q_pos v).le (cone_denom_pos v n.1 (sphere_norm n)).le)
      (hs.nonnegative t ht (x,v)))),hs.particle_cone_identity ht x n.1]

lemma EnergyPrefix.physicalBinDensity_particle_flux {s : Solution} {T t σ : ℝ}
    (hs : EnergyPrefix s T) (hσ : σ∈Icc 0 T) (X V : ℝ→Vec) (C : ClosedConeBin)
    (hq : 0≤C.qmin) (hd : 0≤C.dmin) (n : Sphere) :
    ENNReal.ofReal (C.qmin*C.dmin)*physicalBinDensity s X V C t σ n≤
      ENNReal.ofReal (particleEnergy s (σ,X t-(t-σ) • n.1)-
        dot n.1 (particleFlux s (σ,X t-(t-σ) • n.1))) := by
  rw [←hs.particleCone_lintegral hσ _ n]
  unfold physicalBinDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply le_trans _ (setLIntegral_le_lintegral (coneBinMomentumSet C n.1 (velocity (V t))) _)
  apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
  intro v hv
  rw [←ENNReal.ofReal_mul (mul_nonneg hq hd)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (hs.nonnegative σ hσ _)
  exact mul_le_mul hv.1.1 hv.2.1.1 hd (q_pos v).le

lemma physicalBin_integral_le_cone {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J)
    {g : ConeCoordinate→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻z,g z ∂physicalBinMeasure V B J)≤
      ∫⁻t in J,∫⁻σ in Icc 0 t,∫⁻n : Sphere,g (t,σ,n) ∂sphereMeasure := by
  have hbase := measurableSet_physicalBinBase hV B hJ
  unfold physicalBinMeasure
  rw [←lintegral_indicator hbase,lintegral_prod _ (hg.indicator hbase).aemeasurable]
  rw [←lintegral_indicator hJ]
  apply lintegral_mono
  intro t
  by_cases ht : t∈J
  · rw [indicator_of_mem ht]
    have hm : Measurable (fun p : ℝ×Sphere=>(physicalBinBase V B J).indicator g (t,p)) :=
      (hg.indicator hbase).comp (measurable_const.prodMk measurable_id)
    dsimp only
    rw [lintegral_prod _ hm.aemeasurable,←lintegral_indicator measurableSet_Icc]
    apply lintegral_mono
    intro σ
    by_cases hσ : σ∈Icc 0 t
    · rw [indicator_of_mem hσ]
      exact lintegral_mono (fun n=>indicator_le_self _ _ (t,σ,n))
    · rw [indicator_of_notMem hσ]
      apply le_of_eq
      apply lintegral_eq_zero_of_ae_eq_zero
      exact ae_of_all _ (fun n=>indicator_of_notMem (fun hz=>hσ hz.2.1) _)
  · rw [indicator_of_notMem ht]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ (fun p=>indicator_of_notMem (fun hz=>ht hz.1) _)

def prefixConeDensity (s : Solution) (T : ℝ) (X : ℝ→Vec) (z : ConeCoordinate) : ℝ :=
  goodConeDensity s (prefixClamp T z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1) z.2.2.1

lemma EnergyPrefix.continuous_clamped_goodConeDensity {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) :
    Continuous (fun p : (ℝ×Vec)×Vec=>goodConeDensity s (prefixClamp T p.1.1,p.1.2) p.2) := by
  have hc : Continuous (prefixClamp T) := continuous_const.max (continuous_const.min continuous_id)
  have hmap : Continuous (fun p : (ℝ×Vec)×Vec=>((prefixClamp T p.1.1,p.1.2),p.2)) :=
    ((hc.comp continuous_fst.fst).prodMk continuous_fst.snd).prodMk continuous_snd
  have hh := (hs.goodConeDensity_continuousOn hT).comp_continuous hmap (fun p=>
    ⟨⟨prefixClamp_mem hT p.1.1,mem_univ _⟩,mem_univ _⟩)
  exact hh

lemma EnergyPrefix.measurable_prefixConeDensity {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X : ℝ→Vec} (hX : Measurable X) :
    Measurable (prefixConeDensity s T X) := by
  have hn : Measurable (fun z : ConeCoordinate=>z.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hy : Measurable (fun z : ConeCoordinate=>((z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1),z.2.2.1)) :=
    ((measurable_fst.comp measurable_snd).prodMk
      ((hX.comp measurable_fst).sub ((measurable_fst.sub (measurable_fst.comp measurable_snd)).smul hn))).prodMk hn
  change Measurable ((fun p : (ℝ×Vec)×Vec=>goodConeDensity s (prefixClamp T p.1.1,p.1.2) p.2) ∘
    (fun z : ConeCoordinate=>((z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1),z.2.2.1)))
  exact (hs.continuous_clamped_goodConeDensity hT).measurable.comp hy

lemma EnergyPrefix.physicalBin_radial_density_flux {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hq : 0<B.qmin) (hd : 0<B.dmin) (hr : 0<B.rmin)
    {g : ℝ→ℝ≥0∞} (hg : Measurable g) (hgf : ∀t,g t≠⊤) :
    (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal (z.1-z.2.1)*
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)≤
      (∫⁻t in J,g t)*ENNReal.ofReal (4*(∫y : Vec,totalEnergy s (0,y))/(B.qmin*B.dmin*B.rmin)) := by
  let c := B.qmin*B.dmin*B.rmin
  have hc : 0<c := by dsimp [c]; positivity
  let G : ConeCoordinate→ℝ≥0∞ := fun z=>ENNReal.ofReal c⁻¹*g z.1*
    ENNReal.ofReal ((z.1-z.2.1)^2*prefixConeDensity s T X z)
  have hG : Measurable G :=
    (measurable_const.mul (hg.comp measurable_fst)).mul
      (((measurable_fst.sub (measurable_fst.comp measurable_snd)).pow_const 2).mul
        (hs.measurable_prefixConeDensity hT hX)).ennreal_ofReal
  have hb : (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal (z.1-z.2.1)*
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)≤
      ∫⁻z,G z ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    have hσ : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    have hrz : 0<z.1-z.2.1 := hr.trans_le hz.2.2.1.1
    have hp := hs.physicalBinDensity_particle_flux (t:=z.1) hσ X V B hq.le hd.le z.2.2
    have hdens : ENNReal.ofReal (B.qmin*B.dmin)*
        physicalBinDensity s X V B z.1 z.2.1 z.2.2≤ENNReal.ofReal (prefixConeDensity s T X z) := by
      apply hp.trans
      apply ENNReal.ofReal_le_ofReal
      dsimp [prefixConeDensity,goodConeDensity]
      rw [prefixClamp_eq hσ]
      linarith [sq_nonneg (‖s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)+
        cross z.2.2.1 (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))‖+
        |dot z.2.2.1 (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))|)]
    have hscalar : ENNReal.ofReal (z.1-z.2.1)≤
        ENNReal.ofReal c⁻¹*ENNReal.ofReal ((z.1-z.2.1)^2)*ENNReal.ofReal (B.qmin*B.dmin) := by
      rw [←ENNReal.ofReal_mul (inv_pos.mpr hc).le,←ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      dsimp [c]
      field_simp
      nlinarith [hz.2.2.1.1]
    calc
      _ ≤ g z.1*(ENNReal.ofReal c⁻¹*ENNReal.ofReal ((z.1-z.2.1)^2)*
          ENNReal.ofReal (B.qmin*B.dmin))*physicalBinDensity s X V B z.1 z.2.1 z.2.2 :=
        mul_le_mul' (mul_le_mul' le_rfl hscalar) le_rfl
      _ = (ENNReal.ofReal c⁻¹*g z.1*ENNReal.ofReal ((z.1-z.2.1)^2))*
          (ENNReal.ofReal (B.qmin*B.dmin)*physicalBinDensity s X V B z.1 z.2.1 z.2.2) := by ring
      _ ≤ (ENNReal.ofReal c⁻¹*g z.1*ENNReal.ofReal ((z.1-z.2.1)^2))*
          ENNReal.ofReal (prefixConeDensity s T X z) := mul_le_mul' le_rfl hdens
      _ = G z := by dsimp [G]; rw [ENNReal.ofReal_mul (sq_nonneg _)]; ring
  apply (hb.trans (physicalBin_integral_le_cone hV B hJ hG)).trans
  have hE : 0≤∫y : Vec,totalEnergy s (0,y) :=
    integral_nonneg (fun y=>hs.total_energy_nonneg ⟨le_rfl,hT⟩ y)
  calc
    _ ≤ ∫⁻t in J,ENNReal.ofReal c⁻¹*g t*ENNReal.ofReal (4*(∫y : Vec,totalEnergy s (0,y))) := by
      apply setLIntegral_mono' hJ
      intro t ht
      have htt := hJT ht
      have he : (∫⁻σ in Icc 0 t,∫⁻n : Sphere,G (t,σ,n) ∂sphereMeasure)=
          ENNReal.ofReal c⁻¹*g t*(∫⁻σ in Icc 0 t,∫⁻n : Sphere,
            ENNReal.ofReal (goodConeIntegrand s t (X t) σ n) ∂sphereMeasure) := by
        simp_rw [←lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hgf t))]
        apply setLIntegral_congr_fun measurableSet_Icc
        intro σ hσ
        apply lintegral_congr
        intro n
        dsimp [G,prefixConeDensity,goodConeIntegrand]
        rw [prefixClamp_eq (show σ∈Icc 0 T from ⟨hσ.1,hσ.2.trans htt.2⟩)]
      rw [he,hs.goodConeIntegrand_lintegral_eq htt (X t)]
      apply mul_le_mul' le_rfl
      apply ENNReal.ofReal_le_ofReal
      have hh := EnergyPrefix.goodConeDensity_time_integral_bound (hs.mono htt.2) htt.1 (X t)
      simpa only [intervalIntegral.integral_of_le htt.1,integral_Icc_eq_integral_Ioc,goodConeIntegrand] using hh
    _ = _ := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc
        _ = (∫⁻t in J,g t)*(ENNReal.ofReal c⁻¹*ENNReal.ofReal (4*(∫y : Vec,totalEnergy s (0,y)))) := by ac_rfl
        _ = _ := by
          rw [←ENNReal.ofReal_mul (inv_pos.mpr hc).le]
          congr 2
          dsimp [c]
          ring

def representativeReceiverCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) (g : ℝ→ℝ≥0∞) : ℝ≥0∞ :=
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  ENNReal.ofReal (θ/(w*φ^2)) *
    (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal (z.1-z.2.1)*
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B (Icc a b))

lemma receiver_near_scalar {C H h p θ φ w : ℝ} (hw : 0<w) (hφ : 0<φ) :
    (θ/(w*φ^2))*(49152*C*p^3*θ^2*φ^2*(2*H*h)*(2*H*h-H*h/2))=
      (147456*C*H^2)*(w⁻¹*(h^2*(p*θ)^3)) := by
  field_simp
  ring

lemma receiver_far_scalar {E H h p θ φ w : ℝ} (hE : 0≤E) (hH : 1≤H)
    (hh : 0<h) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hw : 0<w) :
    (θ/(w*φ^2))*(4*E/((p/128)*(θ^2/2)*(H*h/2)))≤
      (2048*E)*(w⁻¹*((p*θ*h*φ^2)⁻¹)) := by
  have hH0 : 0<H := zero_lt_one.trans_le hH
  calc
    _ = ((2048*E)*(w⁻¹*((p*θ*h*φ^2)⁻¹)))/H := by field_simp; ring
    _ ≤ _ := div_le_self (by positivity) hH

lemma Admissible.representative_receiver_envelope {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b w : ℝ) (g : ℝ→ℝ≥0∞),
      0≤a → b≤T → 0<w → Measurable g → (∀t,g t≠⊤) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      representativeReceiverCost s F zX w k a b g≤
        ENNReal.ofReal (C*receiverCoefficient w p θ φ h)*(∫⁻t in Icc a b,g t) := by
  obtain ⟨C₀,hC₀,hden⟩ := hd.uniform_physicalBinDensity_constant
  let E := datumEnergyNumber d
  let Cn := 147456*C₀*(max 1 T₀)^2
  let Cf := 2048*E
  let C := max Cn Cf
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  have hCn : 0≤Cn := by dsimp [Cn]; positivity
  have hCf : 0≤Cf := by dsimp [Cf]; positivity
  have hC : 0≤C := hCn.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro s T F hs hT hTT zX k a b w g ha hb hw hg hgf
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let N := w⁻¹*(h^2*(p*θ)^3)
  let R := w⁻¹*((p*θ*h*φ^2)⁻¹)
  let L := ∫⁻t in Icc a b,g t
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hθ1 : θ≤1 := cappedRepresentative_le_one _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hH0 : 0<H := zero_lt_one.trans_le hH
  have hHH : H ≤ max 1 T₀ := max_le_max le_rfl hTT
  have hN : 0≤N := by dsimp [N]; positivity
  have hR : 0≤R := by dsimp [R]; positivity
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs.energyPrefix hT).comp (continuous_id.prodMk continuous_const)
  have hX : Measurable X := hα.fst.measurable
  have hV : Measurable V := hα.snd.measurable
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hdensity : ∀z∈physicalBinBase V B (Icc a b),
      physicalBinDensity s X V B z.1 z.2.1 z.2.2≤ENNReal.ofReal (128*C₀*p^3*θ^2) := by
    intro z hz
    have hσ : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩
    have hh := hden s T F hs.energyPrefix hs.initial_f X V B z.1 z.2.1 z.2.2
      p θ 1 hσ hp.le hθ.le (by norm_num) (by change p/32≤p; linarith) le_rfl (by norm_num [B,representativeClosedBin])
    simpa only [min_eq_left hθ1] using hh
  have hn := physicalBin_radial_density_near hV B measurableSet_Icc hC₀ hp.le hθ.le hφ.le
    (by change 0≤2*H*h; positivity) le_rfl hdensity hg
  have hf := hs.energyPrefix.physicalBin_radial_density_flux hT hX hV B measurableSet_Icc hJ
    (by change 0<p/128; positivity) (by change 0<θ^2/2; positivity)
    (by change 0<H*h/2; positivity) hg hgf
  rw [hs.initial_energy_eq] at hf
  have hn' : representativeReceiverCost s F zX w k a b g≤ENNReal.ofReal (C*N)*L := by
    unfold representativeReceiverCost
    dsimp only
    apply (mul_le_mul' le_rfl hn).trans
    calc
      _ = ENNReal.ofReal ((147456*C₀*H^2)*N)*L := by
        rw [←mul_assoc,mul_right_comm,←ENNReal.ofReal_mul (by positivity : 0≤θ/(w*φ^2))]
        congr 2
        exact receiver_near_scalar hw hφ
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0.le hHH 2) (by positivity)) (le_max_left _ _)) hN)) le_rfl
  have hf' : representativeReceiverCost s F zX w k a b g≤ENNReal.ofReal (C*R)*L := by
    unfold representativeReceiverCost
    dsimp only
    apply (mul_le_mul' le_rfl hf).trans
    calc
      _ = ENNReal.ofReal ((θ/(w*φ^2))*(4*E/((p/128)*(θ^2/2)*(H*h/2))))*L := by
        rw [←mul_assoc,mul_right_comm,←ENNReal.ofReal_mul (by positivity : 0≤θ/(w*φ^2))]
        rfl
      _ ≤ ENNReal.ofReal (Cf*R)*L := mul_le_mul'
        (ENNReal.ofReal_le_ofReal (receiver_far_scalar hE hH hh hp hθ hφ hw)) le_rfl
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right Cn Cf) hR)) le_rfl
  have hu : receiverCoefficient w p θ φ h=min N R := by
    dsimp [receiverCoefficient,N,R]
    exact mul_min_of_nonneg _ _ (inv_nonneg.mpr hw.le)
  rw [hu,mul_min_of_nonneg _ _ hC,ENNReal.ofReal_min,min_mul]
  exact le_min hn' hf'

lemma Admissible.selected_receiver_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ) (g : ℝ→ℝ≥0∞),
      0≤a → b≤T → 1≤w → w≤P → 0<I → I≤(w/P)^2 →
      Measurable g → (∀t,g t≠⊤) →
      let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>representativeReceiverCost s F zX w k a b g) k)≤
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,g t) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_receiver_envelope T₀
  refine ⟨C*((1-selectionDecay)⁻¹)^4,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [receiverCoefficient_on_selected_bins 512 16384 M A (by norm_num) hM.le hA.le,
    eventually_ge_atTop (1:ℝ)] with P hsafe hP
  intro s T F hs hT hTT zX a b I w g ha hb hw hwP hI hIP hg hgf
  dsimp only
  let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
  let L := ∫⁻t in Icc a b,g t
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hpt (k : Fin 4→ℕ) (hk : k∈Q) :
      representativeReceiverCost s F zX w k a b g≤
        ENNReal.ofReal ((C*w^(-1/2:ℝ))*selectionWeight P (cappedRepresentative (k 1))
          (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))*L := by
    have he := hbound s T F hs hT hTT zX k a b w g ha hb hw0 hg hgf
    have hu := hsafe (sourceRepresentative (k 0)) w (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)) I
      (by unfold sourceRepresentative; positivity) hk.1.1 hw hwP (cappedRepresentative_pos _)
      (cappedRepresentative_pos _) (cappedRepresentative_le_one _) (cappedRepresentative_pos _)
      (cappedRepresentative_le_one _) hI hIP hk.2
    apply he.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hu hC
  have hwgt := selection_weighted_tsum (zero_le_one.trans hP) (by positivity : 0≤C*w^(-1/2:ℝ))
    Q (fun _ hk=>hk.1.1) (fun _ hk=>hk.1.2.1)
    (fun k=>ENNReal.ofReal ((C*w^(-1/2:ℝ))*selectionWeight P (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) (fun _ _=>le_rfl)
  classical
  calc
    _ ≤ ∑'k : Fin 4→ℕ,Q.indicator (fun k=>ENNReal.ofReal ((C*w^(-1/2:ℝ))*
        selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
        (cappedRepresentative (k 3)))*L) k := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈Q
      · change Q.indicator _ k≤_
        simpa only [indicator_of_mem hk] using hpt k hk
      · change Q.indicator _ k≤_
        simp only [indicator_of_notMem hk,le_refl]
    _ = (∑'k : Fin 4→ℕ,Q.indicator (fun k=>ENNReal.ofReal ((C*w^(-1/2:ℝ))*
        selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
        (cappedRepresentative (k 3)))) k)*L := by
      simp_rw [indicator_mul_left]
      exact ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal ((C*w^(-1/2:ℝ))*((1-selectionDecay)⁻¹)^4)*L := mul_le_mul' hwgt le_rfl
    _ = _ := by congr 2; ring

def representativeTimeWeightCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w I : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  ENNReal.ofReal (θ/(I*φ)) *
    (∫⁻z : ConeCoordinate,ENNReal.ofReal (z.1-z.2.1)*
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B (Icc a b))

lemma representativeTimeWeightCost_eq (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) {w I : ℝ} (hw : 0<w) (hI : 0<I) (k : Fin 4→ℕ) (a b : ℝ) :
    representativeTimeWeightCost s F zX w I k a b=
      ENNReal.ofReal (w*cappedRepresentative (k 2)/I)*
        representativeReceiverCost s F zX w k a b (fun _=>1) := by
  have hφ := cappedRepresentative_pos (k 2)
  unfold representativeTimeWeightCost representativeReceiverCost
  dsimp only
  simp only [one_mul]
  rw [←mul_assoc,←ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

lemma Admissible.time_weight_bin_near {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      representativeTimeWeightCost s F zX w I k a b≤
        ENNReal.ofReal (C*(cappedRepresentative (k 3))^2*(sourceRepresentative (k 0))^3*
          (cappedRepresentative (k 1))^3*cappedRepresentative (k 2)) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_receiver_envelope T₀
  refine ⟨C,hC,?_⟩
  intro s T F hs hT hTT zX k a b I w ha hb hab hI hJI hw
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have he := hbound s T F hs hT hTT zX k a b w (fun _=>1) ha hb hw measurable_const (by simp)
  dsimp only at he
  rw [lintegral_const,one_mul,Measure.restrict_apply_univ,Real.volume_Icc] at he
  rw [representativeTimeWeightCost_eq s F zX hw hI]
  apply (mul_le_mul' le_rfl he).trans
  calc
    _≤ENNReal.ofReal (w*φ/I)*(ENNReal.ofReal (C*(w⁻¹*(h^2*(p*θ)^3)))*ENNReal.ofReal I) := by
      apply mul_le_mul' le_rfl
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (inv_nonneg.mpr hw.le)) hC))
        (ENNReal.ofReal_le_ofReal hJI)
    _=ENNReal.ofReal (C*h^2*p^3*θ^3*φ) := by
      rw [←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

lemma Admissible.selected_long_time_weight_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k ∧
        I<cappedRepresentative (k 3)}
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>representativeTimeWeightCost s F zX w I k a b) k)≤
        ENNReal.ofReal (C*P*Real.sqrt I) := by
  obtain ⟨C,hC,hbound⟩ := hd.time_weight_bin_near T₀
  refine ⟨C*((1-selectionDecay)⁻¹)^4,by positivity,?_⟩
  intro M A P hP s T F hs hT hTT zX a b I w ha hb hab hI hJI hw
  dsimp only
  let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k ∧
    I<cappedRepresentative (k 3)}
  have hbnd (k : Fin 4→ℕ) (hk : k∈Q) :
      representativeTimeWeightCost s F zX w I k a b≤ENNReal.ofReal ((C*P*Real.sqrt I)*
        selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2)) (cappedRepresentative (k 3))) := by
    have hp : 0<sourceRepresentative (k 0) := by unfold sourceRepresentative; positivity
    have hμ := (pureOccupationEnvelope_bounds P 512 16384 M A (sourceRepresentative (k 0)) w
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)) I).1
    rw [max_eq_right hk.2.2.le] at hμ
    have he := selected_long_time_weight_scalar hP hp hk.1.1 (cappedRepresentative_pos _)
      (cappedRepresentative_pos _) (cappedRepresentative_le_one _) (cappedRepresentative_pos _)
      (cappedRepresentative_le_one _) hI hμ (lt_min_iff.mp hk.2.1).1 (lt_min_iff.mp hk.2.1).2
    apply (hbound s T F hs hT hTT zX k a b I w ha hb hab hI hJI hw).trans
    exact ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he hC)
  have hh := selection_weighted_tsum hP.le (by positivity : 0≤C*P*Real.sqrt I) Q
    (fun _ hk=>hk.1.1) (fun _ hk=>hk.1.2.1)
    (fun k=>representativeTimeWeightCost s F zX w I k a b) hbnd
  convert hh using 1
  congr 1
  ring

lemma representativeTimeWeightCost_le_central {s : Solution} {T a b w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (k : Fin 4→ℕ) (hI : 0<I)
    (hh : cappedRepresentative (k 3)≤I)
    (hθφ : cappedRepresentative (k 1)≤cappedRepresentative (k 2)) :
    representativeTimeWeightCost s F zX w I k a b≤
      ENNReal.ofReal (2*max 1 T)*representativeCentralCost s F zX w k a b := by
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hφ : 0<φ := cappedRepresentative_pos _
  have hθ : 0<θ := cappedRepresentative_pos _
  have hpos : 0<h := cappedRepresentative_pos _
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hc : (θ/(I*φ))*B.rmax≤2*max 1 T := by
    change (θ/(I*φ))*(2*max 1 T*h)≤_
    have ht : θ/φ≤1 := (div_le_one hφ).mpr hθφ
    have hr : h/I≤1 := (div_le_one hI).mpr hh
    have hprod : (θ/φ)*(h/I)≤1 := calc
      _≤1*(h/I) := mul_le_mul_of_nonneg_right ht (by positivity)
      _≤1 := by simpa only [one_mul] using hr
    calc
      _=(2*max 1 T)*((θ/φ)*(h/I)) := by ring
      _≤(2*max 1 T)*1 := mul_le_mul_of_nonneg_left
        hprod (by positivity)
      _=_ := mul_one _
  unfold representativeTimeWeightCost representativeCentralCost
  dsimp only
  change ENNReal.ofReal (θ/(I*φ))*(∫⁻z : ConeCoordinate,ENNReal.ofReal (z.1-z.2.1)*
    physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B (Icc a b))≤_
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hα.snd.measurable B measurableSet_Icc)] with z hz
  apply (mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hz.2.2.1.2) le_rfl)).trans
  rw [←mul_assoc,←ENNReal.ofReal_mul (by positivity : 0≤θ/(I*φ))]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl

lemma Admissible.selected_time_weight_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 1≤w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>representativeTimeWeightCost s F zX w I k a b) k)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.central_uniform T₀
  obtain ⟨Cl,hCl,hlong⟩ := hd.selected_long_time_weight_uniform T₀
  let K := 2*max 1 T₀
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨K*Cc+Cl,by positivity,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP HZ
  dsimp only
  let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
  let Ql := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k ∧
    I<cappedRepresentative (k 3)}
  let fc := fun k=>representativeCentralCost s F zX w k a b
  let ft := fun k=>representativeTimeWeightCost s F zX w I k a b
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hfirst : P*Real.sqrt I≤B := by
    exact le_add_of_nonneg_right (by positivity)
  have hpoint (k : Fin 4→ℕ) : Q.indicator ft k≤
      ENNReal.ofReal K*(centralIndexSector P).indicator fc k+Ql.indicator ft k := by
    by_cases hk : k∈Q
    · rw [indicator_of_mem hk]
      by_cases hh : I<cappedRepresentative (k 3)
      · have hkl : k∈Ql := ⟨hk.1,hk.2,hh⟩
        rw [indicator_of_mem hkl]
        exact le_add_of_nonneg_left (show (0:ℝ≥0∞)≤_ from bot_le)
      · have hc : k∈centralIndexSector P := representativeSmallSector_subset_centralIndexSector P hk.1
        rw [indicator_of_mem hc]
        have ht := representativeTimeWeightCost_le_central (a:=a) (b:=b) (w:=w) F hs.energyPrefix hT zX k hI
          (le_of_not_gt hh) (hk.1.2.2.trans (by have hφ := (cappedRepresentative_pos (k 2)).le; linarith))
        apply ht.trans
        have hKT : (2*max 1 T:ℝ)≤K := by dsimp [K]; gcongr
        apply (mul_le_mul' (ENNReal.ofReal_le_ofReal hKT) le_rfl).trans
        exact le_add_of_nonneg_right (show (0:ℝ≥0∞)≤_ from bot_le)
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hc := hcentral M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
  dsimp only at hc
  rw [←tsum_centralIndexSector P (fun k=>representativeCentralCost s F zX w k a b)] at hc
  have hl := hlong M A P (zero_lt_one.trans_le hP) s T F hs hT hTT zX a b I w ha hb hab hI hJI
    (zero_lt_one.trans_le hw)
  change (∑'k,Q.indicator ft k)≤_
  calc
    _≤∑'k,(ENNReal.ofReal K*(centralIndexSector P).indicator fc k+Ql.indicator ft k) :=
      ENNReal.tsum_le_tsum hpoint
    _=ENNReal.ofReal K*(∑'k,(centralIndexSector P).indicator fc k)+(∑'k,Ql.indicator ft k) := by
      rw [ENNReal.tsum_add,ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal K*ENNReal.ofReal (Cc*B)+ENNReal.ofReal (Cl*(P*Real.sqrt I)) := by
      exact add_le_add (mul_le_mul' le_rfl hc) (by simpa only [mul_assoc] using hl)
    _≤ENNReal.ofReal K*ENNReal.ofReal (Cc*B)+ENNReal.ofReal (Cl*B) :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hfirst hCl))
    _=ENNReal.ofReal ((K*Cc+Cl)*B) := by
      rw [←ENNReal.ofReal_mul hK,←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma PhaseFlowOn.bulkRemainder_density {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (hw : 0<w)
    (Q : Set (Fin 4→ℕ)) {J : Set ℝ} (hJT : J⊆Icc 0 T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈J,‖W t‖≤1)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16)
    {z : ConeCoordinate} (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) J) :
    (∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (remainderConeKernel s F.flow zX) W J (z,v)‖)≤
      ENNReal.ofReal 147*physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2+
      ENNReal.ofReal (15424*(cappedRepresentative (k 1)/(w*(cappedRepresentative (k 2))^2)))*
        (ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX z.1‖*ENNReal.ofReal (z.1-z.2.1)*
          physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
            (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
  let c := 15424*(cappedRepresentative (k 1)/(w*(cappedRepresentative (k 2))^2))
  have hc : 0≤c := by dsimp [c]; positivity
  have hcoeff : 0≤147+c*‖prefixMomentumForce s F.flow T zX z.1‖*(z.1-z.2.1) := by positivity
  have hb : (∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (remainderConeKernel s F.flow zX) W J (z,v)‖)≤
      ENNReal.ofReal (147+c*‖prefixMomentumForce s F.flow T zX z.1‖*(z.1-z.2.1))*
        physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2 := by
    unfold physicalBinDensity
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
    intro v hv
    rw [←ENNReal.ofReal_mul hcoeff]
    apply ENNReal.ofReal_le_ofReal
    have hcost {radius density theta phi speed : ℝ} {normal momentum receiver force : Vec}
        (hnormal : ‖normal‖=1) (hradius : 0<radius) (hdensity : 0≤density)
        (htheta : 0<theta) (hphi : 0<phi) (hspeed : 0<speed)
        (hsector : theta≤phi/16)
        (hdeficit : 1-dot normal (velocity momentum)∈Icc (theta^2/2) (8*theta^2))
        (hreceiver : 1-dot normal (velocity receiver)∈Icc (phi^2/2) (8*phi^2))
        (hquantum : speed/8≤q receiver) :
        ‖(density*(1-dot normal (velocity receiver))) •
          normalisedRemainder radius (velocity receiver) (velocity momentum) normal
            (fderiv ℝ velocity receiver force)‖≤
          147*density+15424*(theta/(speed*phi^2))*‖force‖*radius*density := by
      have hsector' : theta≤phi := by linarith
      have hnormalBound {input : Vec} {angle : ℝ} (hangle : 0≤angle)
          (hbound : 1-dot normal (velocity input)≤8*angle^2) :
          ‖velocity input-normal‖≤4*angle := by
        apply norm_sub_le_of_deficit (norm_velocity_lt_one input).le hnormal.le (by positivity)
        rw [dot_comm]
        nlinarith
      have hmomentum := hnormalBound htheta.le hdeficit.2
      have hreceiverNorm := hnormalBound hphi.le hreceiver.2
      have hdifference := small_deficit_difference hnormal htheta.le hphi.le hsector'
        (cone_denom_pos momentum normal hnormal).le hdeficit.2 hmomentum hreceiverNorm
      have hremainder := signedRemainder_small_norm receiver force (velocity momentum) normal
        hradius hdensity hnormal htheta.le hphi hsector' hreceiver.1 hreceiver.2
        hmomentum hdifference
      have hforce : ‖force‖/q receiver≤8*‖force‖/speed := by
        calc
          _≤‖force‖/(speed/8) := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hquantum
          _=_ := by ring
      rw [normalisedRemainder_eq _ _ _ _ hradius.ne',
        smul_comm (density*(1-dot normal (velocity receiver))),
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg radius)]
      calc
        _≤radius^2*(147*density/radius^2+1928*density*theta*(‖force‖/q receiver)/(radius*phi^2)) :=
          mul_le_mul_of_nonneg_left hremainder (sq_nonneg radius)
        _≤radius^2*(147*density/radius^2+1928*density*theta*(8*‖force‖/speed)/(radius*phi^2)) := by
          gcongr
        _=_ := by field_simp; ring
    have htime := hJT hz.1
    have hsourceTime : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans htime.2⟩
    have hdensity := hs.nonnegative _ hsourceTime
      ((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)
    by_cases hphase : (z,v)∈trianglePhaseDomain T
    · have hflow : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
        simp only [prefixFlow,prefixClamp_eq htime]
      have hforce : prefixMomentumForce s F.flow T zX z.1=
          (lorentzField s.E s.B (z.1,F.flow zX z.1)).2 := by
        simp only [prefixMomentumForce,hflow,prefixClamp_eq htime]
      have hdeficit : 1-dot z.2.2.1 (velocity (F.flow zX z.1).2)∈
          Icc ((cappedRepresentative (k 2))^2/2) (8*(cappedRepresentative (k 2))^2) := by
        simpa only [hflow,representativeClosedBin] using hz.2.2.2.2
      have hquantum : w/8≤q (F.flow zX z.1).2 := by
        simpa only [hflow,representativeClosedBin] using hz.2.2.2.1.1
      dsimp only
      rw [hflow] at hv ⊢
      rw [hforce]
      apply (selectedConeTriangle_norm_le Q (remainderConeKernel s F.flow zX) W J (z,v)).trans
      rw [indicator_of_mem hz.1]
      apply ((W z.1).le_opNorm _).trans
      apply (mul_le_mul_of_nonneg_right (hW _ hz.1) (norm_nonneg _)).trans
      rw [one_mul,triangleConeKernel,indicator_of_mem hphase,smul_smul,mul_comm]
      have hbound := hcost (force := (lorentzField s.E s.B (z.1,F.flow zX z.1)).2)
        (sphere_norm z.2.2) (sub_pos.mpr hphase.2.2)
        (by simpa only [hflow] using hdensity) hθ hφ hw hsmall hv.2.1 hdeficit hquantum
      simp only [triangleKernelState,remainderConeKernel,phaseAcceleration,lorentzField,lorentzPhase] at hbound ⊢
      convert hbound using 1
      dsimp [c]
      ring
    · simp only [selectedConeTriangle,triangleConeKernel,indicator_of_notMem hphase,map_zero,norm_zero]
      positivity
  apply hb.trans_eq
  rw [ENNReal.ofReal_add (by norm_num) (by positivity),add_mul,
    ENNReal.ofReal_mul (mul_nonneg hc (norm_nonneg _)),ENNReal.ofReal_mul hc]
  simp only [c,mul_assoc]

lemma PhaseFlowOn.bulkRemainder_bin_integral {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hw : 0<w)
    (Q : Set (Fin 4→ℕ)) {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈Icc a b,‖W t‖≤1)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16) :
    (∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
        (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q
        (remainderConeKernel s F.flow zX) W (Icc a b) (z,v)‖
      ∂volume ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal 147*representativeCentralCost s F zX w k a b+
      ENNReal.ofReal 15424*representativeReceiverCost s F zX w k a b
        (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hX : Measurable (fun t=>(prefixFlow F.flow T zX t).1) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).fst.measurable
  have hN := physicalBinDensity_aemeasurable hs hT hX hV (representativeClosedBin T w k)
    measurableSet_Icc (Icc_subset_Icc ha hb)
  have hcost := fun z hz=>F.bulkRemainder_density hs zX hw Q (Icc_subset_Icc ha hb) W hW k hsmall (z:=z) hz
  have hbnd := setLIntegral_mono' (μ:=volume.prod (volume.prod sphereMeasure)) (measurableSet_physicalBinBase hV (representativeClosedBin T w k) measurableSet_Icc) hcost
  apply hbnd.trans_eq
  unfold physicalBinMeasure at hN
  rw [lintegral_add_left' (hN.const_mul _),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold representativeCentralCost representativeReceiverCost
  dsimp only
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤15424),mul_assoc]
  rfl

lemma PhaseFlowOn.bulkRate_bin_integral {s : Solution} {T w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hI : 0<I)
    (Q : Set (Fin 4→ℕ)) {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈Icc a b,‖W t‖≤1)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16) :
    (∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
        (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q
        (fun p=>I⁻¹ • normalisedRatePrimitive F.flow zX p) W (Icc a b) (z,v)‖
      ∂volume ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal 52*representativeTimeWeightCost s F zX w I k a b := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  rw [representativeTimeWeightCost,←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤52)]
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' (measurableSet_physicalBinBase hV _ measurableSet_Icc)
  intro z hz
  unfold physicalBinDensity
  rw [←mul_assoc,←lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
  intro v hv
  have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
  have hn : 0≤52*(cappedRepresentative (k 1)/(I*cappedRepresentative (k 2))) := by positivity
  rw [←ENNReal.ofReal_mul hn,←ENNReal.ofReal_mul (mul_nonneg hn hr)]
  apply ENNReal.ofReal_le_ofReal
  have hcost {radius density theta phi duration : ℝ} {normal momentum receiver : Vec}
      (hnormal : ‖normal‖=1) (hradius : 0<radius) (hdensity : 0≤density)
      (htheta : 0<theta) (hphi : 0<phi) (hphiOne : phi≤1) (hduration : 0<duration)
      (hsector : theta≤phi/16)
      (hdeficit : 1-dot normal (velocity momentum)∈Icc (theta^2/2) (8*theta^2))
      (hreceiver : 1-dot normal (velocity receiver)∈Icc (phi^2/2) (8*phi^2)) :
      ‖(density*(1-dot normal (velocity receiver))) •
        (duration⁻¹ • (((1-dot normal (velocity momentum))/(1-dot normal (velocity receiver))) •
          normalisedPrimitive radius (velocity receiver) (velocity momentum) normal))‖≤
        52*(theta/(duration*phi))*radius*density := by
    have hsector' : theta≤phi := by linarith
    have hnormalBound {input : Vec} {angle : ℝ} (hangle : 0≤angle)
        (hbound : 1-dot normal (velocity input)≤8*angle^2) :
        ‖velocity input-normal‖≤4*angle := by
      apply norm_sub_le_of_deficit (norm_velocity_lt_one input).le hnormal.le (by positivity)
      rw [dot_comm]
      nlinarith
    have hmomentum := hnormalBound htheta.le hdeficit.2
    have hreceiverNorm := hnormalBound hphi.le hreceiver.2
    have hdifference := small_deficit_difference hnormal htheta.le hphi.le hsector'
      (cone_denom_pos momentum normal hnormal).le hdeficit.2 hmomentum hreceiverNorm
    have hprimitive := small_primitive_norm hnormal htheta.le hphi hphiOne hreceiver.1
      hmomentum hdifference
    have hdenom := (cone_denom_pos momentum normal hnormal).ne'
    have hreceiverDenom := (cone_denom_pos receiver normal hnormal).ne'
    have hscalar : (density*(1-dot normal (velocity receiver)))*duration⁻¹*
        ((1-dot normal (velocity momentum))/(1-dot normal (velocity receiver)))*
          (radius/(1-dot normal (velocity momentum)))=density*radius/duration := by field_simp
    simp only [normalisedPrimitive,smul_smul]
    rw [show (density*(1-dot normal (velocity receiver)))*
      (duration⁻¹*((1-dot normal (velocity momentum))/(1-dot normal (velocity receiver))*
        (radius/(1-dot normal (velocity momentum)))))=density*radius/duration by
      convert hscalar using 1
      ring]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤density*radius/duration)]
    calc
      _≤(density*radius/duration)*(52*theta/phi) := mul_le_mul_of_nonneg_left hprimitive (by positivity)
      _=_ := by ring
  have htime := (Icc_subset_Icc ha hb) hz.1
  have hsourceTime : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans htime.2⟩
  have hdensity := hs.nonnegative _ hsourceTime
    ((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)
  by_cases hphase : (z,v)∈trianglePhaseDomain T
  · have hflow : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
      simp only [prefixFlow,prefixClamp_eq htime]
    have hdeficit : 1-dot z.2.2.1 (velocity (F.flow zX z.1).2)∈
        Icc ((cappedRepresentative (k 2))^2/2) (8*(cappedRepresentative (k 2))^2) := by
      simpa only [hflow,representativeClosedBin] using hz.2.2.2.2
    dsimp only
    rw [hflow] at hv ⊢
    apply (selectedConeTriangle_norm_le Q
      (fun state=>I⁻¹ • normalisedRatePrimitive F.flow zX state) W (Icc a b) (z,v)).trans
    rw [indicator_of_mem hz.1]
    apply ((W z.1).le_opNorm _).trans
    apply (mul_le_mul_of_nonneg_right (hW _ hz.1) (norm_nonneg _)).trans
    rw [one_mul,triangleConeKernel,indicator_of_mem hphase,smul_smul,mul_comm]
    simpa only [triangleKernelState,normalisedRatePrimitive] using
      hcost (sphere_norm z.2.2) (sub_pos.mpr hphase.2.2)
        (by simpa only [hflow] using hdensity) hθ hφ (cappedRepresentative_le_one _)
        hI hsmall hv.2.1 hdeficit
  · simp only [selectedConeTriangle,triangleConeKernel,indicator_of_notMem hphase,map_zero,norm_zero]
    positivity

end RVM

end

end OAI
