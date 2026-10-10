import OAI.Probability.FKMaps.BridgeLimit

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

def clipTime (x : ℝ) : unitInterval := projIcc 0 1 zero_le_one x

@[fun_prop] lemma continuous_clipTime : Continuous clipTime := continuous_projIcc (h := zero_le_one)

lemma clipTime_coe (t : unitInterval) : clipTime (t:ℝ)=t :=
  projIcc_val _ t

lemma clipTime_of_nonpos {x : ℝ} (hx : x ≤ 0) : clipTime x=0 :=
  projIcc_of_le_left _ hx

lemma clipTime_of_one_le {x : ℝ} (hx : 1 ≤ x) : clipTime x=1 :=
  projIcc_of_right_le _ hx

def cyclePath (c : unitInterval) (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) where
  toFun t := f (clipTime ((c:ℝ)+(t:ℝ)))+
    f (clipTime ((c:ℝ)+(t:ℝ)-1))-f 0-f c
  continuous_toFun := by
    apply Continuous.sub _ continuous_const
    apply Continuous.sub _ continuous_const
    exact (f.continuous.comp (continuous_clipTime.comp (continuous_const.add continuous_subtype_val))).add
      (f.continuous.comp (continuous_clipTime.comp ((continuous_const.add continuous_subtype_val).sub continuous_const)))

lemma cyclePath_zero (c : unitInterval) (f : C(unitInterval,ℝ)) : cyclePath c f 0=0 := by
  change f (clipTime ((c:ℝ)+0))+f (clipTime ((c:ℝ)+0-1))-f 0-f c=0
  rw [add_zero,clipTime_coe,clipTime_of_nonpos (by linarith [c.property.2])]
  ring

lemma cyclePath_one (c : unitInterval) (f : C(unitInterval,ℝ)) :
    cyclePath c f 1=f 1-f 0 := by
  change f (clipTime ((c:ℝ)+1))+f (clipTime ((c:ℝ)+1-1))-f 0-f c=f 1-f 0
  rw [clipTime_of_one_le (by linarith [c.property.1]),add_sub_cancel_right,clipTime_coe]
  ring

lemma cyclePath_apply_left (c t : unitInterval) (f : C(unitInterval,ℝ))
    (h : (c:ℝ)+(t:ℝ) ≤ 1) :
    cyclePath c f t=f ⟨(c:ℝ)+(t:ℝ),add_nonneg c.property.1 t.property.1,h⟩-f c := by
  change f (clipTime ((c:ℝ)+(t:ℝ)))+f (clipTime ((c:ℝ)+(t:ℝ)-1))-f 0-f c=_
  rw [show clipTime ((c:ℝ)+(t:ℝ))=⟨(c:ℝ)+(t:ℝ),add_nonneg c.property.1 t.property.1,h⟩ from
    projIcc_of_mem _ ⟨add_nonneg c.property.1 t.property.1,h⟩,
    clipTime_of_nonpos (by linarith)]
  ring

lemma cyclePath_apply_right (c t : unitInterval) (f : C(unitInterval,ℝ))
    (h : 1 ≤ (c:ℝ)+(t:ℝ)) :
    cyclePath c f t=f 1+f ⟨(c:ℝ)+(t:ℝ)-1,by linarith,by linarith [c.property.2,t.property.2]⟩-f 0-f c := by
  change f (clipTime ((c:ℝ)+(t:ℝ)))+f (clipTime ((c:ℝ)+(t:ℝ)-1))-f 0-f c=_
  rw [clipTime_of_one_le h]
  have hh : clipTime ((c:ℝ)+(t:ℝ)-1)=
      ⟨(c:ℝ)+(t:ℝ)-1,by linarith,by linarith [c.property.2,t.property.2]⟩ :=
    projIcc_of_mem zero_le_one ⟨by linarith,by linarith [c.property.2,t.property.2]⟩
  rw [hh]

lemma continuous_cyclePath : Continuous (fun z : unitInterval × C(unitInterval,ℝ) => cyclePath z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (unitInterval × C(unitInterval,ℝ)) × unitInterval =>
    z.1.2 (clipTime ((z.1.1:ℝ)+(z.2:ℝ)))+
      z.1.2 (clipTime ((z.1.1:ℝ)+(z.2:ℝ)-1))-z.1.2 0-z.1.2 z.1.1)
  have h₁ : Continuous (fun z : (unitInterval × C(unitInterval,ℝ)) × unitInterval =>
    clipTime ((z.1.1:ℝ)+(z.2:ℝ))) := by fun_prop
  have h₂ : Continuous (fun z : (unitInterval × C(unitInterval,ℝ)) × unitInterval =>
    clipTime ((z.1.1:ℝ)+(z.2:ℝ)-1)) := by fun_prop
  apply Continuous.sub _ (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
    (continuous_fst.comp continuous_fst)))
  apply Continuous.sub _ (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_const))
  exact (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk h₁)).add
    (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk h₂))

lemma cyclePath_nonneg (f : C(unitInterval,ℝ)) (c : unitInterval)
    (hc : ∀ t, f c ≤ f t) (hf : f 0=f 1) : ∀ t, 0 ≤ cyclePath c f t := by
  intro t
  by_cases h : (c:ℝ)+(t:ℝ) ≤ 1
  · rw [cyclePath_apply_left c t f h]
    exact sub_nonneg.mpr (hc _)
  · rw [cyclePath_apply_right c t f (le_of_not_ge h)]
    linarith [hc ⟨(c:ℝ)+(t:ℝ)-1,by linarith,by linarith [c.property.2,t.property.2]⟩]

lemma exists_minTime (f : C(unitInterval,ℝ)) : ∃ c, ∀ t, f c ≤ f t := by
  obtain ⟨c,_,hc⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set unitInterval).Nonempty)
    f.continuous.continuousOn
  exact ⟨c,fun t => hc (mem_univ t)⟩

lemma exists_firstMinimum (f : C(unitInterval,ℝ)) :
    ∃ c, (∀ t, f c ≤ f t) ∧ ∀ d, (∀ t, f d ≤ f t) → c ≤ d := by
  obtain ⟨d,hd⟩ := exists_minTime f
  have hK : IsCompact {t | f t=f d} := (isClosed_eq f.continuous continuous_const).isCompact
  obtain ⟨c,hc,hleast⟩ := hK.exists_isLeast ⟨d,rfl⟩
  refine ⟨c,fun t => hc.trans_le (hd t),?_⟩
  intro e he
  exact hleast (le_antisymm (he d) (hd e))

def minTime (f : C(unitInterval,ℝ)) : unitInterval := (exists_firstMinimum f).choose

lemma minTime_spec (f : C(unitInterval,ℝ)) : ∀ t, f (minTime f) ≤ f t :=
  (exists_firstMinimum f).choose_spec.1

lemma minTime_first (f : C(unitInterval,ℝ)) (d : unitInterval) (hd : ∀ t, f d ≤ f t) :
    minTime f ≤ d := (exists_firstMinimum f).choose_spec.2 d hd

def UniqueMinimum (f : C(unitInterval,ℝ)) (c : unitInterval) : Prop :=
  (∀ t, f c ≤ f t) ∧ ∀ t, f t=f c → t=c

lemma minimum_stable {f : C(unitInterval,ℝ)} {c : unitInterval}
    (hc : UniqueMinimum f c) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ>0, ∀ g : C(unitInterval,ℝ), dist g f<δ →
      ∀ d : unitInterval, (∀ t, g d ≤ g t) → dist d c<ε := by
  let K : Set unitInterval := {d | ε ≤ dist d c}
  have hK : IsCompact K := (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  have hgap : ∀ d ∈ K, f c < f d := by
    intro d hd
    apply lt_of_le_of_ne (hc.1 d)
    intro heq
    have hdc := hc.2 d heq.symm
    subst d
    exact (not_le_of_gt hε) (by simpa [K] using hd)
  obtain ⟨a,ha,hKa⟩ := hK.exists_forall_le' f.continuous.continuousOn hgap
  refine ⟨(a-f c)/3,by linarith,?_⟩
  intro g hg d hd
  by_contra hdc
  have hda : a ≤ f d := hKa d (not_lt.mp hdc)
  have hh (u : unitInterval) : |g u-f u| < (a-f c)/3 :=
    (show |g u-f u| ≤ dist g f from by simpa only [Real.dist_eq] using
      (ContinuousMap.dist_apply_le_dist (f := g) (g := f) u)).trans_lt hg
  have h₁ := hh d
  have h₂ := hh c
  have h₃ := hd c
  have h₄ := abs_lt.mp h₁
  have h₅ := abs_lt.mp h₂
  linarith

lemma continuousAt_minTime {f : C(unitInterval,ℝ)} {c : unitInterval}
    (hc : UniqueMinimum f c) : ContinuousAt minTime f := by
  have heq : minTime f=c := hc.2 _ (le_antisymm (minTime_spec f c) (hc.1 _))
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,hδ'⟩ := minimum_stable hc hε
  exact ⟨δ,hδ,fun g hg => heq ▸ hδ' g hg (minTime g) (minTime_spec g)⟩

def vervaat (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) := cyclePath (minTime f) f

lemma continuousAt_vervaat {f : C(unitInterval,ℝ)} {c : unitInterval}
    (hc : UniqueMinimum f c) : ContinuousAt vervaat f :=
  continuous_cyclePath.continuousAt.comp ((continuousAt_minTime hc).prodMk continuousAt_id)

lemma vervaat_zero (f : C(unitInterval,ℝ)) : vervaat f 0=0 := cyclePath_zero _ _

lemma vervaat_one (f : C(unitInterval,ℝ)) : vervaat f 1=f 1-f 0 := cyclePath_one _ _

lemma vervaat_nonneg (f : C(unitInterval,ℝ)) (hf : f 0=f 1) : ∀ t, 0 ≤ vervaat f t :=
  cyclePath_nonneg f (minTime f) (minTime_spec f) hf

def restrictedMin (K : Set unitInterval) (hK : IsCompact K) (hne : K.Nonempty)
    (f : C(unitInterval,ℝ)) : ℝ :=
  f (hK.exists_isMinOn hne f.continuous.continuousOn).choose

lemma restrictedMin_spec (K : Set unitInterval) (hK : IsCompact K) (hne : K.Nonempty)
    (f : C(unitInterval,ℝ)) :
    (∃ c ∈ K, restrictedMin K hK hne f=f c) ∧ ∀ c ∈ K, restrictedMin K hK hne f ≤ f c := by
  have h := (hK.exists_isMinOn hne f.continuous.continuousOn).choose_spec
  exact ⟨⟨_,h.1,rfl⟩,h.2⟩

lemma restrictedMin_lipschitz (K : Set unitInterval) (hK : IsCompact K) (hne : K.Nonempty) :
    LipschitzWith 1 (restrictedMin K hK hne) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul,Real.dist_eq]
  obtain ⟨⟨a,ha,hea⟩,hfa⟩ := restrictedMin_spec K hK hne f
  obtain ⟨⟨b,hb,heb⟩,hgb⟩ := restrictedMin_spec K hK hne g
  have h₁ := hfa b hb
  have h₂ := hgb a ha
  have h₃ := ContinuousMap.dist_apply_le_dist (f := f) (g := g) a
  have h₄ := ContinuousMap.dist_apply_le_dist (f := f) (g := g) b
  rw [Real.dist_eq] at h₃ h₄
  rw [abs_le]
  constructor <;> linarith [le_abs_self (f a-g a),neg_abs_le (f a-g a),
    le_abs_self (f b-g b),neg_abs_le (f b-g b)]

lemma minTime_le_iff (a : unitInterval) (f : C(unitInterval,ℝ)) :
    minTime f ≤ a ↔ restrictedMin (Iic a) isClosed_Iic.isCompact ⟨0,a.property.1⟩ f =
      restrictedMin univ isCompact_univ univ_nonempty f := by
  obtain ⟨⟨b,hb,heb⟩,hgb⟩ := restrictedMin_spec (Iic a) isClosed_Iic.isCompact ⟨0,a.property.1⟩ f
  obtain ⟨⟨c,_,hec⟩,hfc⟩ := restrictedMin_spec univ isCompact_univ univ_nonempty f
  constructor
  · intro ha
    apply le_antisymm
    · exact (hgb (minTime f) ha).trans ((minTime_spec f c).trans_eq hec.symm)
    · exact hfc b (mem_univ b) |>.trans_eq heb.symm
  · intro hh
    apply (minTime_first f b _).trans hb
    intro t
    rw [← heb,hh]
    exact hfc t (mem_univ t)

lemma measurable_minTime : Measurable minTime := by
  apply measurable_of_Iic
  intro a
  have heq : minTime ⁻¹' Iic a =
    {f | restrictedMin (Iic a) isClosed_Iic.isCompact ⟨0,a.property.1⟩ f =
      restrictedMin univ isCompact_univ univ_nonempty f} := by
    ext f
    exact minTime_le_iff a f
  rw [heq]
  exact measurableSet_eq_fun (restrictedMin_lipschitz _ _ _).continuous.measurable
    (restrictedMin_lipschitz _ _ _).continuous.measurable

lemma measurable_vervaat : Measurable vervaat :=
  continuous_cyclePath.measurable.comp (measurable_minTime.prodMk measurable_id)

def reversePath (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) :=
  f.comp ⟨unitInterval.symm,unitInterval.continuous_symm⟩

lemma reversePath_apply (f : C(unitInterval,ℝ)) (t : unitInterval) :
    reversePath f t=f (unitInterval.symm t) := rfl

lemma reversePath_lipschitz : LipschitzWith 1 reversePath := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  exact ContinuousMap.dist_apply_le_dist (unitInterval.symm t)

def lastMinTime (f : C(unitInterval,ℝ)) : unitInterval :=
  unitInterval.symm (minTime (reversePath f))

lemma lastMinTime_spec (f : C(unitInterval,ℝ)) : ∀ t, f (lastMinTime f) ≤ f t := by
  intro t
  have hh := minTime_spec (reversePath f) (unitInterval.symm t)
  simpa only [reversePath_apply,unitInterval.symm_symm,lastMinTime] using hh

lemma lastMinTime_last (f : C(unitInterval,ℝ)) (d : unitInterval) (hd : ∀ t, f d ≤ f t) :
    d ≤ lastMinTime f := by
  apply unitInterval.symm_le_symm.mp
  simp only [lastMinTime,unitInterval.symm_symm]
  apply minTime_first
  intro t
  simpa only [reversePath_apply,unitInterval.symm_symm] using hd (unitInterval.symm t)

lemma measurable_lastMinTime : Measurable lastMinTime :=
  unitInterval.continuous_symm.measurable.comp (measurable_minTime.comp reversePath_lipschitz.continuous.measurable)

def HasUniqueMinimum (f : C(unitInterval,ℝ)) : Prop := ∃ c, UniqueMinimum f c

lemma hasUniqueMinimum_iff (f : C(unitInterval,ℝ)) :
    HasUniqueMinimum f ↔ minTime f=lastMinTime f := by
  constructor
  · rintro ⟨c,hc⟩
    have hh (d : unitInterval) (hd : ∀ t, f d ≤ f t) : d=c :=
      hc.2 d (le_antisymm (hd c) (hc.1 d))
    exact (hh _ (minTime_spec f)).trans (hh _ (lastMinTime_spec f)).symm
  · intro heq
    refine ⟨minTime f,minTime_spec f,?_⟩
    intro t ht
    have hh : ∀ s, f t ≤ f s := fun s => ht.trans_le (minTime_spec f s)
    exact le_antisymm ((lastMinTime_last f t hh).trans_eq heq.symm) (minTime_first f t hh)

lemma measurableSet_hasUniqueMinimum : MeasurableSet {f : C(unitInterval,ℝ) | HasUniqueMinimum f} := by
  simp_rw [hasUniqueMinimum_iff]
  exact measurableSet_eq_fun measurable_minTime measurable_lastMinTime

def tiltPath (a : ℝ) (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) :=
  f+a • ⟨Subtype.val,continuous_subtype_val⟩

lemma tiltPath_apply (a : ℝ) (f : C(unitInterval,ℝ)) (t : unitInterval) :
    tiltPath a f t=f t+a*(t:ℝ) := rfl

lemma continuous_tiltPath : Continuous (fun z : C(unitInterval,ℝ) × ℝ => tiltPath z.2 z.1) :=
  continuous_fst.add (continuous_snd.smul continuous_const)

def TiltMinimum (f : unitInterval → ℝ) (a : ℝ) (t : unitInterval) : Prop :=
  ∀ s, f t+a*(t:ℝ) ≤ f s+a*(s:ℝ)

lemma tiltMinimum_antitone {f : unitInterval → ℝ} {a b : ℝ} (hab : a<b)
    {s t : unitInterval} (hs : TiltMinimum f a s) (ht : TiltMinimum f b t) : t ≤ s := by
  have h₁ := hs t
  have h₂ := ht s
  change (t:ℝ) ≤ (s:ℝ)
  by_contra hts
  have hp : 0 < (b-a)*((t:ℝ)-(s:ℝ)) := mul_pos (sub_pos.mpr hab) (sub_pos.mpr (lt_of_not_ge hts))
  nlinarith

theorem countable_badTilts (f : unitInterval → ℝ) :
    Set.Countable {a : ℝ | ∃ s t : unitInterval, s<t ∧ TiltMinimum f a s ∧ TiltMinimum f a t} := by
  let D := {a : ℝ // ∃ s t : unitInterval, s<t ∧ TiltMinimum f a s ∧ TiltMinimum f a t}
  have hex (a : D) : ∃ q : ℚ, ∃ s t : unitInterval,
      (s:ℝ)<q ∧ (q:ℝ)<t ∧ TiltMinimum f a s ∧ TiltMinimum f a t := by
    obtain ⟨s,t,hst,hs,ht⟩ := a.property
    obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn (show (s:ℝ)<t from hst)
    exact ⟨q,s,t,hq₁,hq₂,hs,ht⟩
  choose q hq using hex
  have hinj : Function.Injective q := by
    intro a b hab
    by_contra hne
    obtain ⟨s,t,hsq,hqt,hs,ht⟩ := hq a
    obtain ⟨u,v,huq,hqv,hu,hv⟩ := hq b
    have hne' : (a:ℝ) ≠ (b:ℝ) := fun hh => hne (Subtype.ext hh)
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hh := tiltMinimum_antitone hlt hs hv
      have : (v:ℝ) ≤ s := hh
      rw [hab] at hsq
      linarith
    · have hh := tiltMinimum_antitone hgt hu ht
      have : (t:ℝ) ≤ u := hh
      rw [hab] at hqt
      linarith
  exact @Set.to_countable ℝ _ (Function.Injective.countable hinj)

lemma not_unique_iff_two_minima (f : C(unitInterval,ℝ)) :
    ¬ HasUniqueMinimum f ↔ ∃ s t, s<t ∧ (∀ u, f s ≤ f u) ∧ (∀ u, f t ≤ f u) := by
  rw [hasUniqueMinimum_iff]
  constructor
  · intro h
    exact ⟨minTime f,lastMinTime f,lt_of_le_of_ne (minTime_first f _ (lastMinTime_spec f)) h,
      minTime_spec f,lastMinTime_spec f⟩
  · rintro ⟨s,t,hst,hs,ht⟩ heq
    have h₁ := minTime_first f s hs
    have h₂ := lastMinTime_last f t ht
    rw [heq] at h₁
    exact (not_le_of_gt hst) (h₂.trans h₁)

theorem ae_unique_minimum_tilt (μ : Measure C(unitInterval,ℝ)) (ν : Measure ℝ)
    [SFinite μ] [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ z ∂μ.prod ν, HasUniqueMinimum (tiltPath z.2 z.1) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_hasUniqueMinimum.preimage continuous_tiltPath.measurable)).mpr
  apply ae_of_all
  intro f
  rw [ae_iff]
  change ν {a | ¬ HasUniqueMinimum (tiltPath a f)}=0
  have heq : {a | ¬ HasUniqueMinimum (tiltPath a f)}=
      {a : ℝ | ∃ s t : unitInterval, s<t ∧ TiltMinimum f a s ∧ TiltMinimum f a t} := by
    ext a
    simp only [mem_ofPred_eq,not_unique_iff_two_minima,TiltMinimum,tiltPath_apply]
  rw [heq]
  exact (countable_badTilts f).measure_zero ν

theorem IndepFun.ae_unique_minimum_tilt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → C(unitInterval,ℝ)} {A : Ω → ℝ}
    (hX : AEMeasurable X P) (hA : AEMeasurable A P) (h : IndepFun X A P)
    [NullSingletonClass (P.map A)] :
    ∀ᵐ ω ∂P, HasUniqueMinimum (tiltPath (A ω) (X ω)) := by
  have heq := h.map_prod_eq_prod_map_map hX hA
  have hu := FKCRT.TreeCoding.ae_unique_minimum_tilt (P.map X) (P.map A)
  rw [← heq] at hu
  exact (ae_map_iff (hX.prodMk hA)
    (measurableSet_hasUniqueMinimum.preimage continuous_tiltPath.measurable)).mp hu

theorem brownian_unique_minimum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, HasUniqueMinimum (brownianPath B ω) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hA : P.map (B 1)=gaussianReal 0 1 := (hB.hasLaw_eval 1).map_eq
  have : NullSingletonClass (P.map (B 1)) := by
    rw [hA]
    exact nullSingletonClass_gaussianReal one_ne_zero
  have hu := IndepFun.ae_unique_minimum_tilt (bridgePath_aemeasurable hB)
    (hB.aemeasurable 1) (bridgePath_indep_endpoint hB)
  filter_upwards [hu] with ω hω
  convert hω using 1
  simp [tiltPath,bridgePath,sub_add_cancel]

lemma indepFun_path_of_coords {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → C(unitInterval,ℝ)} {A : Ω → ℝ}
    (h : IndepFun (fun ω t => X ω t) A P) : IndepFun X A P := by
  let D := TopologicalSpace.denseSeq unitInterval
  let f : C(unitInterval,ℝ) → (ℕ → ℝ) := fun g n => g (D n)
  have hf : MeasurableEmbedding f := by
    apply Continuous.measurableEmbedding
    · apply continuous_pi
      intro n
      fun_prop
    · intro a b hab
      apply ContinuousMap.ext
      exact congrFun ((TopologicalSpace.denseRange_denseSeq unitInterval).equalizer
        a.continuous b.continuous hab)
  exact indepFun_of_measurableEmbedding_left hf (h.comp
    (φ := fun a : unitInterval → ℝ => fun n : ℕ => a (D n)) (by fun_prop) measurable_id)

def prefixTimePath (a : unitInterval) (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) :=
  f.comp ⟨fun t => a*t,by fun_prop⟩

lemma prefixTimePath_apply (a t : unitInterval) (f : C(unitInterval,ℝ)) :
    prefixTimePath a f t=f (a*t) := rfl

lemma prefixTimePath_lipschitz (a : unitInterval) : LipschitzWith 1 (prefixTimePath a) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  exact ContinuousMap.dist_apply_le_dist (a*t)

def prefixResidual {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (a : unitInterval) (ω : Ω) :
    C(unitInterval,ℝ) := prefixTimePath a (brownianPath B ω)-
      B ⟨(a:ℝ),a.property.1⟩ ω • ⟨Subtype.val,continuous_subtype_val⟩

def bridgeAt {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (a : unitInterval) (ω : Ω) : ℝ :=
  B ⟨(a:ℝ),a.property.1⟩ ω-(a:ℝ)*B 1 ω

lemma prefixResidual_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (a : unitInterval) :
    AEMeasurable (prefixResidual B a) P :=
  ((prefixTimePath_lipschitz a).continuous.measurable.comp_aemeasurable
    (brownianPath_aemeasurable hB)).sub ((hB.aemeasurable _).smul aemeasurable_const)

lemma prefixResidual_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (a : unitInterval) :
    ∀ᵐ ω ∂P, ∀ t : unitInterval, prefixResidual B a ω t=
      B ⟨(a:ℝ)*(t:ℝ),mul_nonneg a.property.1 t.property.1⟩ ω-
        (t:ℝ)*B ⟨(a:ℝ),a.property.1⟩ ω := by
  filter_upwards [brownianPath_ae_eq hB] with ω hω
  intro t
  simp only [prefixResidual,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
    prefixTimePath_apply,ContinuousMap.coe_mk,smul_eq_mul,hω,Set.Icc.coe_mul,mul_comm]

lemma prefixResidual_joint_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a : unitInterval) :
    IsGaussianProcess (Sum.elim
      (fun (t : unitInterval) ω =>
        B ⟨(a:ℝ)*(t:ℝ),mul_nonneg a.property.1 t.property.1⟩ ω-
          (t:ℝ)*B ⟨(a:ℝ),a.property.1⟩ ω)
      (fun (_ : Unit) ω => bridgeAt B a ω)) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro s
  cases s with
  | inl t =>
    let u : ℝ≥0 := ⟨(a:ℝ)*(t:ℝ),mul_nonneg a.property.1 t.property.1⟩
    let v : ℝ≥0 := ⟨(a:ℝ),a.property.1⟩
    refine ⟨{u,v},
      { toFun x := x ⟨u,by simp⟩-(t:ℝ)*x ⟨v,by simp⟩
        map_add' x y := by simp only [Pi.add_apply]; ring
        map_smul' c x := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring },?_⟩
    intro ω
    rfl
  | inr t =>
    let v : ℝ≥0 := ⟨(a:ℝ),a.property.1⟩
    refine ⟨{v,1},
      { toFun x := x ⟨v,by simp⟩-(a:ℝ)*x ⟨1,by simp⟩
        map_add' x y := by simp only [Pi.add_apply]; ring
        map_smul' c x := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring },?_⟩
    intro ω
    rfl

lemma prefixResidual_covariance_bridgeAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a t : unitInterval) :
    cov[fun ω => B ⟨(a:ℝ)*(t:ℝ),mul_nonneg a.property.1 t.property.1⟩ ω-
      (t:ℝ)*B ⟨(a:ℝ),a.property.1⟩ ω,bridgeAt B a; P]=0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm (s : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  let u : ℝ≥0 := ⟨(a:ℝ)*(t:ℝ), mul_nonneg (unitInterval.nonneg a) (unitInterval.nonneg t)⟩
  let v : ℝ≥0 := ⟨(a:ℝ), unitInterval.nonneg a⟩
  change cov[fun ω => B u ω - (t:ℝ)*B v ω,
    fun ω => B v ω - (a:ℝ)*B 1 ω; P] = 0
  rw [covariance_fun_sub_fun_sub (hm _) ((hm _).const_mul _) (hm _) ((hm _).const_mul _),
    covariance_const_mul_right,covariance_const_mul_left,covariance_const_mul_left,
    covariance_const_mul_right]
  simp only [hB.covariance_eval]
  have h₁ : (a:ℝ)*(t:ℝ) ≤ a := mul_le_of_le_one_right a.property.1 t.property.2
  have h₂ : (a:ℝ)*(t:ℝ) ≤ 1 := h₁.trans a.property.2
  change min ((a:ℝ)*(t:ℝ)) (a:ℝ)-(a:ℝ)*min ((a:ℝ)*(t:ℝ)) 1-
    (t:ℝ)*min (a:ℝ) (a:ℝ)+(t:ℝ)*((a:ℝ)*min (a:ℝ) 1)=0
  rw [min_eq_left h₁,min_eq_left h₂,min_self,min_eq_left a.property.2]
  ring

lemma prefixResidual_indep_bridgeAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (a : unitInterval) :
    IndepFun (prefixResidual B a) (bridgeAt B a) P := by
  apply indepFun_path_of_coords
  have hi := (prefixResidual_joint_gaussian hB.toIsPreBrownianReal a).indepFun_of_covariance_eq_zero
    (fun t => (hB.aemeasurable _).sub ((hB.aemeasurable _).const_mul _))
    (fun _ => (hB.aemeasurable _).sub ((hB.aemeasurable _).const_mul _))
    (fun t _ => prefixResidual_covariance_bridgeAt hB.toIsPreBrownianReal a t)
  have he := hi.comp measurable_id (measurable_pi_apply ())
  apply he.congr ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [prefixResidual_ae_eq hB a] with ω hω
  exact funext (fun t => (hω t).symm)

lemma variance_bridgeAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a : unitInterval) :
    Var[bridgeAt B a; P]=(a:ℝ)*(1-(a:ℝ)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm (s : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  let u : ℝ≥0 := ⟨(a:ℝ), unitInterval.nonneg a⟩
  change Var[fun ω => B u ω - (a:ℝ)*B 1 ω; P] = _
  rw [variance_fun_sub (hm _) ((hm _).const_mul _),variance_const_mul,
    covariance_const_mul_right,← covariance_self (hm _).aemeasurable,
    ← covariance_self (hm _).aemeasurable]
  simp only [hB.covariance_eval,min_self,NNReal.coe_one]
  change (a:ℝ)-2*((a:ℝ)*min (a:ℝ) 1)+(a:ℝ)^2*1=_
  rw [min_eq_left a.property.2]
  ring

lemma bridgeAt_nullSingletonClass {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {a : unitInterval}
    (ha₀ : 0 < a) (ha₁ : a < 1) : NullSingletonClass (P.map (bridgeAt B a)) := by
  have hg := (prefixResidual_joint_gaussian hB.toIsPreBrownianReal a).hasGaussianLaw_eval (Sum.inr ())
  change HasGaussianLaw (bridgeAt B a) P at hg
  rw [hg.map_eq_gaussianReal,variance_bridgeAt hB.toIsPreBrownianReal a]
  apply nullSingletonClass_gaussianReal
  exact ne_of_gt (Real.toNNReal_pos.mpr (mul_pos ha₀ (sub_pos.mpr ha₁)))

theorem bridge_prefix_unique_minimum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {a : unitInterval}
    (ha₀ : 0 < a) (ha₁ : a < 1) :
    ∀ᵐ ω ∂P, HasUniqueMinimum (prefixTimePath a (bridgePath B ω)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have := bridgeAt_nullSingletonClass hB ha₀ ha₁
  have hA : AEMeasurable (bridgeAt B a) P :=
    (hB.aemeasurable _).sub ((hB.aemeasurable _).const_mul _)
  have hu := IndepFun.ae_unique_minimum_tilt (prefixResidual_aemeasurable hB a) hA
    (prefixResidual_indep_bridgeAt hB a)
  filter_upwards [hu] with ω hω
  convert hω using 1
  apply ContinuousMap.ext
  intro t
  simp only [prefixTimePath_apply,bridgePath,prefixResidual,tiltPath_apply,bridgeAt,
    ContinuousMap.sub_apply,ContinuousMap.smul_apply,ContinuousMap.coe_mk,smul_eq_mul,Set.Icc.coe_mul]
  ring

theorem gaussianProcess_map_eq {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : T → Ω → ℝ} (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P)
    (hm : ∀ t, P[X t]=P[Y t])
    (hc : ∀ s t, cov[X s,X t; P]=cov[Y s,Y t; P])
    (hXm : AEMeasurable (fun ω t => X t ω) P)
    (hYm : AEMeasurable (fun ω t => Y t ω) P) :
    P.map (fun ω t => X t ω)=P.map (fun ω t => Y t ω) := by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  apply (map_eq_iff_forall_finset_map_restrict_eq hXm hYm).mpr
  intro I
  apply (MeasurableEquiv.toLp 2 (I → ℝ)).map_measurableEquiv_injective
  rw [MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ]
  have := (hX.hasGaussianLaw I).isGaussian_map
  have := (hY.hasGaussianLaw I).isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map,integral_map,integral_map,integral_map]
    · simp only [id_eq]
      rw [ContinuousLinearEquiv.integral_comp_comm,
        ContinuousLinearEquiv.integral_comp_comm]
      congr 1
      ext i
      rw [eval_integral,eval_integral]
      · exact hm i
      · exact fun j => (hY.hasGaussianLaw_eval j).integrable
      · exact fun j => (hX.hasGaussianLaw_eval j).integrable
    any_goals fun_prop
    · exact AEMeasurable.of_eval fun _ => hY.aemeasurable _
    · exact AEMeasurable.of_eval fun _ => hX.aemeasurable _
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
      isPosSemidef_covarianceBilin.isSymm fun x => ?_
    simp only [ContinuousLinearMap.toBilinForm_apply]
    rw [PiLp.coe_symm_continuousLinearEquiv,covarianceBilin_apply_pi,covarianceBilin_apply_pi]
    · congrm ∑ i, ∑ j, _ * ?_
      rw [covariance_map,covariance_map]
      · exact hc _ _
      any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
      · exact AEMeasurable.of_eval fun _ => hY.aemeasurable _
      · exact AEMeasurable.of_eval fun _ => hX.aemeasurable _
    · exact fun i => ((hY.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two
    · exact fun i => ((hX.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two

lemma path_law_eq_of_coords {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → C(unitInterval,ℝ)} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (heq : P.map (fun ω (n : ℕ) => X ω (TopologicalSpace.denseSeq unitInterval n))=
      P.map (fun ω (n : ℕ) => Y ω (TopologicalSpace.denseSeq unitInterval n))) :
    P.map X=P.map Y := by
  let f : C(unitInterval,ℝ) → (ℕ → ℝ) := fun g n => g (TopologicalSpace.denseSeq unitInterval n)
  have hf : MeasurableEmbedding f := by
    apply Continuous.measurableEmbedding
    · apply continuous_pi
      intro n
      fun_prop
    · intro a b hab
      apply ContinuousMap.ext
      exact congrFun ((TopologicalSpace.denseRange_denseSeq unitInterval).equalizer
        a.continuous b.continuous hab)
  apply hf.map_injective
  rw [AEMeasurable.map_map_of_aemeasurable hf.measurable.aemeasurable hX,
    AEMeasurable.map_map_of_aemeasurable hf.measurable.aemeasurable hY]
  exact heq

def circleTime (c t : unitInterval) : unitInterval :=
  if h : (c:ℝ)+(t:ℝ) ≤ 1 then
    ⟨(c:ℝ)+(t:ℝ),add_nonneg c.property.1 t.property.1,h⟩
  else ⟨(c:ℝ)+(t:ℝ)-1,by linarith,by linarith [c.property.2,t.property.2]⟩

lemma cyclePath_apply_closed (c t : unitInterval) (f : C(unitInterval,ℝ))
    (hf : f 0=f 1) : cyclePath c f t=f (circleTime c t)-f c := by
  unfold circleTime
  split_ifs with h
  · exact cyclePath_apply_left c t f h
  · rw [cyclePath_apply_right c t f (le_of_not_ge h)]
    rw [hf]
    ring

def bbCov (s t : ℝ) : ℝ := min s t-s*t

lemma bbCov_comm (s t : ℝ) : bbCov s t=bbCov t s := by simp [bbCov,min_comm,mul_comm]

lemma circleTime_covariance (c s t : unitInterval) :
    bbCov (circleTime c s) (circleTime c t)-bbCov (circleTime c s) c-
      bbCov c (circleTime c t)+bbCov c c=bbCov s t := by
  wlog hst : s ≤ t generalizing s t
  · rw [bbCov_comm (s:ℝ) (t:ℝ)]
    rw [bbCov_comm (circleTime c s) (circleTime c t),bbCov_comm (circleTime c s) c,
      bbCov_comm c (circleTime c t)]
    convert this t s (le_of_not_ge hst) using 1; ring
  have hc₀ := c.property.1
  have hc₁ := c.property.2
  have hs₀ := s.property.1
  have hs₁ := s.property.2
  have ht₀ := t.property.1
  have ht₁ := t.property.2
  have hst' : (s:ℝ) ≤ t := hst
  by_cases ht : (c:ℝ)+(t:ℝ) ≤ 1
  · have hs : (c:ℝ)+(s:ℝ) ≤ 1 := by linarith
    simp only [circleTime,dite_eq_left hs,dite_eq_left ht,bbCov,min_self]
    rw [min_eq_left (by linarith),min_eq_right (by linarith),min_eq_left (by linarith),
      min_eq_left hst']
    ring
  · by_cases hs : (c:ℝ)+(s:ℝ) ≤ 1
    · simp only [circleTime,dite_eq_left hs,dite_eq_right ht,bbCov,min_self]
      rw [min_eq_right (by linarith),min_eq_right (by linarith),min_eq_right (by linarith),
        min_eq_left hst']
      ring
    · simp only [circleTime,dite_eq_right hs,dite_eq_right ht,bbCov,min_self]
      rw [min_eq_left (by linarith),min_eq_left (by linarith),min_eq_right (by linarith),
        min_eq_left hst']
      ring

lemma circleTime_surj_mod_endpoints (c u : unitInterval) :
    ∃ t, circleTime c t=u ∨ circleTime c t=1 ∧ u=0 := by
  by_cases hcu : c ≤ u
  · let t : unitInterval := ⟨(u:ℝ)-(c:ℝ),sub_nonneg.mpr hcu,by linarith [u.property.2,c.property.1]⟩
    refine ⟨t,Or.inl ?_⟩
    have ht : (c:ℝ)+(t:ℝ) ≤ 1 := by dsimp [t]; linarith [u.property.2]
    simp only [circleTime,dite_eq_left ht]
    apply Subtype.ext
    dsimp [t]
    ring
  · have huc : (u:ℝ) < c := lt_of_not_ge hcu
    let t : unitInterval := ⟨1+(u:ℝ)-(c:ℝ),by linarith [u.property.1,c.property.2],by linarith⟩
    refine ⟨t,?_⟩
    by_cases hu : u=0
    · right
      refine ⟨?_,hu⟩
      have ht : (c:ℝ)+(t:ℝ)=1 := by dsimp [t]; simp [hu]
      simp only [circleTime,ht,le_refl,dite_eq_left]
      rfl
    · left
      have hu₀ : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
      have ht : ¬ (c:ℝ)+(t:ℝ) ≤ 1 := by dsimp [t]; linarith
      simp only [circleTime,dite_eq_right ht]
      apply Subtype.ext
      dsimp [t]
      ring

lemma cycle_min_zero_iff (c : unitInterval) (f : C(unitInterval,ℝ)) (hf : f 0=f 1) :
    (∀ t, cyclePath c f 0 ≤ cyclePath c f t) ↔ ∀ t, f c ≤ f t := by
  rw [cyclePath_zero]
  constructor
  · intro h u
    obtain ⟨t,ht | ⟨ht,hu⟩⟩ := circleTime_surj_mod_endpoints c u
    · have hh := h t
      rw [cyclePath_apply_closed c t f hf,ht] at hh
      linarith
    · have hh := h t
      rw [cyclePath_apply_closed c t f hf,ht,← hf,← hu] at hh
      linarith
  · intro h t
    rw [cyclePath_apply_closed c t f hf]
    exact sub_nonneg.mpr (h _)

lemma bridgeAt_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsGaussianProcess (bridgeAt B) P :=
  (bridge_joint_gaussian hB).comp_right Sum.inl

lemma integral_bridgeAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a : unitInterval) :
    P[bridgeAt B a]=0 := by
  let u : ℝ≥0 := ⟨(a:ℝ), unitInterval.nonneg a⟩
  change (∫ ω, B u ω - (a:ℝ)*B 1 ω ∂P) = 0
  rw [integral_sub (hB.isGaussianProcess.hasGaussianLaw_eval _).integrable
    ((hB.isGaussianProcess.hasGaussianLaw_eval _).integrable.const_mul _),
    integral_const_mul,hB.integral_eval,hB.integral_eval,mul_zero,sub_zero]

lemma covariance_bridgeAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a b : unitInterval) :
    cov[bridgeAt B a,bridgeAt B b; P]=bbCov a b := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm (s : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  let u : ℝ≥0 := ⟨(a:ℝ), unitInterval.nonneg a⟩
  let v : ℝ≥0 := ⟨(b:ℝ), unitInterval.nonneg b⟩
  change cov[fun ω => B u ω - (a:ℝ)*B 1 ω,
    fun ω => B v ω - (b:ℝ)*B 1 ω; P] = _
  rw [covariance_fun_sub_fun_sub (hm _) ((hm _).const_mul _) (hm _) ((hm _).const_mul _),
    covariance_const_mul_right,covariance_const_mul_left,covariance_const_mul_left,
    covariance_const_mul_right]
  simp only [hB.covariance_eval]
  change min (a:ℝ) (b:ℝ)-(b:ℝ)*min (a:ℝ) 1-(a:ℝ)*min 1 (b:ℝ)+
    (a:ℝ)*((b:ℝ)*min 1 1)=_
  rw [min_eq_left a.property.2,min_eq_right b.property.2,min_self]
  dsimp [bbCov]
  ring

lemma cyclicBridge_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (c : unitInterval) :
    IsGaussianProcess (fun t ω => bridgeAt B (circleTime c t) ω-bridgeAt B c ω) P := by
  classical
  apply (bridgeAt_gaussian hB).of_isGaussianProcess
  intro t
  refine ⟨{circleTime c t,c},
    { toFun x := x ⟨circleTime c t,by simp⟩-x ⟨c,by simp⟩
      map_add' x y := by simp only [Pi.add_apply]; ring
      map_smul' a x := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring },?_⟩
  intro ω
  rfl

lemma bridgePath_closed {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, bridgePath B ω 0=0 ∧ bridgePath B ω 1=0 := by
  filter_upwards [bridgePath_ae_eq hB,hB.eval_zero_ae_eq_zero] with ω hω h₀
  constructor
  · have e := hω 0
    change bridgePath B ω 0=B 0 ω-(0:ℝ)*B 1 ω at e
    simpa only [h₀,zero_mul,sub_zero] using e
  · have e := hω 1
    change bridgePath B ω 1=B 1 ω-(1:ℝ)*B 1 ω at e
    simpa only [one_mul,sub_self] using e

theorem bridgePath_cycle_invariant {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (c : unitInterval) :
    P.map (fun ω => cyclePath c (bridgePath B ω))=P.map (bridgePath B) := by
  have hgc := cyclicBridge_gaussian hB.toIsPreBrownianReal c
  have hgb := bridgeAt_gaussian hB.toIsPreBrownianReal
  have hc : Continuous (cyclePath c) := continuous_cyclePath.comp (continuous_const.prodMk continuous_id)
  have hcm := hc.measurable.comp_aemeasurable (bridgePath_aemeasurable hB)
  apply path_law_eq_of_coords hcm (bridgePath_aemeasurable hB)
  let d := TopologicalSpace.denseSeq unitInterval
  have he := gaussianProcess_map_eq (hgc.comp_right d) (hgb.comp_right d)
    (fun n => by
      change P[fun ω => bridgeAt B (circleTime c (d n)) ω-bridgeAt B c ω]=P[bridgeAt B (d n)]
      rw [integral_sub (hgb.hasGaussianLaw_eval _).integrable
        (hgb.hasGaussianLaw_eval _).integrable,integral_bridgeAt hB.toIsPreBrownianReal,
        integral_bridgeAt hB.toIsPreBrownianReal,integral_bridgeAt hB.toIsPreBrownianReal,sub_self])
    (fun n m => by
      have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
      have hm (t : unitInterval) := (hgb.hasGaussianLaw_eval t).memLp_two
      change cov[fun ω => bridgeAt B (circleTime c (d n)) ω-bridgeAt B c ω,
        fun ω => bridgeAt B (circleTime c (d m)) ω-bridgeAt B c ω; P]=
          cov[bridgeAt B (d n),bridgeAt B (d m); P]
      rw [covariance_fun_sub_fun_sub (hm _) (hm _) (hm _) (hm _)]
      simp only [covariance_bridgeAt hB.toIsPreBrownianReal]
      exact circleTime_covariance c (d n) (d m))
    (AEMeasurable.of_eval fun index => hgc.aemeasurable (d index))
    (AEMeasurable.of_eval fun index => hgb.aemeasurable (d index))
  have he₁ : (fun ω n => cyclePath c (bridgePath B ω) (d n)) =ᵐ[P]
      (fun ω n => bridgeAt B (circleTime c (d n)) ω-bridgeAt B c ω) := by
    filter_upwards [bridgePath_ae_eq hB,bridgePath_closed hB] with ω hω hclosed
    funext n
    rw [cyclePath_apply_closed c (d n) _ (hclosed.1.trans hclosed.2.symm),hω _,hω _]
    rfl
  have he₂ : (fun ω n => bridgePath B ω (d n)) =ᵐ[P] (fun ω n => bridgeAt B (d n) ω) := by
    filter_upwards [bridgePath_ae_eq hB] with ω hω
    funext n
    exact hω _
  exact (Measure.map_congr he₁).trans (he.trans (Measure.map_congr he₂).symm)

def minAtSet (c : unitInterval) : Set C(unitInterval,ℝ) := {f | ∀ t, f c ≤ f t}

lemma isClosed_minAtSet (c : unitInterval) : IsClosed (minAtSet c) := by
  simpa only [minAtSet,ofPred_forall] using
    (isClosed_iInter fun t : unitInterval =>
      isClosed_le (by fun_prop : Continuous (fun f : C(unitInterval,ℝ) => f c))
        (by fun_prop : Continuous (fun f : C(unitInterval,ℝ) => f t)))

lemma measurableSet_minAtSet (c : unitInterval) : MeasurableSet (minAtSet c) :=
  (isClosed_minAtSet c).measurableSet

lemma measure_minAt_eq {ν : Measure C(unitInterval,ℝ)}
    (hclosed : ∀ᵐ f ∂ν, f 0=f 1)
    (hc : ∀ c, ν.map (cyclePath c)=ν) (c : unitInterval) :
    ν (minAtSet c)=ν (minAtSet 0) := by
  have hcont : Continuous (cyclePath c) :=
    continuous_cyclePath.comp (continuous_const.prodMk continuous_id)
  calc ν (minAtSet c)=ν ((cyclePath c) ⁻¹' minAtSet 0) := by
         apply measure_congr
         filter_upwards [hclosed] with f hf
         exact propext (cycle_min_zero_iff c f hf).symm
       _=(ν.map (cyclePath c)) (minAtSet 0) :=
         (Measure.map_apply hcont.measurable (measurableSet_minAtSet 0)).symm
       _=ν (minAtSet 0) := by rw [hc]

lemma eq_of_minima_in_unique_prefix {f : C(unitInterval,ℝ)} {a x y : unitInterval}
    (ha : 0 < a) (hu : HasUniqueMinimum (prefixTimePath a f))
    (hx : f ∈ minAtSet x) (hy : f ∈ minAtSet y) (hxa : x ≤ a) (hya : y ≤ a) : x=y := by
  let u : unitInterval := ⟨(x:ℝ)/(a:ℝ),div_nonneg x.property.1 (le_of_lt ha),
    (div_le_one₀ ha).mpr hxa⟩
  let v : unitInterval := ⟨(y:ℝ)/(a:ℝ),div_nonneg y.property.1 (le_of_lt ha),
    (div_le_one₀ ha).mpr hya⟩
  have hau : a*u=x := by apply Subtype.ext; dsimp [u]; field_simp [ne_of_gt ha]
  have hav : a*v=y := by apply Subtype.ext; dsimp [v]; field_simp [ne_of_gt ha]
  obtain ⟨c,hc,huniq⟩ := hu
  have hue := huniq u (le_antisymm (by simpa [prefixTimePath_apply,hau] using hx (a*c)) (hc u))
  have hve := huniq v (le_antisymm (by simpa [prefixTimePath_apply,hav] using hy (a*c)) (hc v))
  rw [← hau,← hav,hue,hve]

def reciprocalTime (n : ℕ) : unitInterval :=
  ⟨1/((n:ℝ)+2),by positivity,by rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg n (α := ℝ)]⟩

lemma reciprocalTime_le_half (n : ℕ) : (reciprocalTime n:ℝ) ≤ 1/2 := by
  apply one_div_le_one_div_of_le (by norm_num)
  linarith [Nat.cast_nonneg n (α := ℝ)]

lemma reciprocalTime_injective : Function.Injective reciprocalTime := by
  intro n m h
  have he := congrArg (fun x : unitInterval => (x:ℝ)) h
  change 1/((n:ℝ)+2)=1/((m:ℝ)+2) at he
  have hnm : (n:ℝ)+2=(m:ℝ)+2 := by simpa only [one_div,inv_inj] using he
  exact_mod_cast (add_right_cancel hnm)

lemma minAt_zero_null_of_cyclic_prefix {ν : Measure C(unitInterval,ℝ)} [IsFiniteMeasure ν]
    (hclosed : ∀ᵐ f ∂ν, f 0=f 1)
    (hcyclic : ∀ c, ν.map (cyclePath c)=ν)
    (hprefix : ∀ᵐ f ∂ν, HasUniqueMinimum (prefixTimePath ⟨1/2,by norm_num,by norm_num⟩ f)) :
    ν (minAtSet 0)=0 := by
  let a : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
  let G : Set C(unitInterval,ℝ) := {f | HasUniqueMinimum (prefixTimePath a f)}
  have hG : MeasurableSet G := measurableSet_hasUniqueMinimum.preimage
    (prefixTimePath_lipschitz a).continuous.measurable
  let E : ℕ → Set C(unitInterval,ℝ) := fun n => minAtSet (reciprocalTime n) ∩ G
  have hE : ∀ n, MeasurableSet (E n) := fun n => (measurableSet_minAtSet _).inter hG
  have hd : Pairwise (fun n m => Disjoint (E n) (E m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro f hfn hfm
    apply hnm
    apply reciprocalTime_injective
    exact eq_of_minima_in_unique_prefix (by change (0:ℝ)<1/2; norm_num) hfn.2 hfn.1 hfm.1
      (reciprocalTime_le_half n) (reciprocalTime_le_half m)
  have hmass (n : ℕ) : ν (E n)=ν (minAtSet 0) := by
    refine (measure_congr ?_).trans (measure_minAt_eq hclosed hcyclic (reciprocalTime n))
    filter_upwards [hprefix] with f hf
    exact propext (and_iff_left hf)
  have hf := measure_ne_top ν (⋃ n, E n)
  rw [measure_iUnion hd hE] at hf
  simp_rw [hmass] at hf
  by_contra hn
  exact hf (ENNReal.tsum_const_eq_top_of_ne_zero hn)

lemma bridgePath_law_cyclic {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (c : unitInterval) :
    (P.map (bridgePath B)).map (cyclePath c)=P.map (bridgePath B) := by
  have hcont : Continuous (cyclePath c) :=
    continuous_cyclePath.comp (continuous_const.prodMk continuous_id)
  rw [AEMeasurable.map_map_of_aemeasurable hcont.measurable.aemeasurable
    (bridgePath_aemeasurable hB)]
  exact bridgePath_cycle_invariant hB c

theorem bridge_not_minimum_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ¬ ∀ t, bridgePath B ω 0 ≤ bridgePath B ω t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let ν := P.map (bridgePath B)
  have : IsProbabilityMeasure ν := inferInstance
  have hclosed : ∀ᵐ f ∂ν, f 0=f 1 := by
    apply (ae_map_iff (bridgePath_aemeasurable hB)
      (measurableSet_eq_fun
        ((by fun_prop : Continuous (fun f : C(unitInterval,ℝ) => f 0)).measurable)
        ((by fun_prop : Continuous (fun f : C(unitInterval,ℝ) => f 1)).measurable))).mpr
    filter_upwards [bridgePath_closed hB] with ω hω
    exact hω.1.trans hω.2.symm
  have hp : ∀ᵐ f ∂ν, HasUniqueMinimum (prefixTimePath ⟨1/2,by norm_num,by norm_num⟩ f) := by
    apply (ae_map_iff (bridgePath_aemeasurable hB)
      (measurableSet_hasUniqueMinimum.preimage
        (prefixTimePath_lipschitz _).continuous.measurable)).mpr
    exact bridge_prefix_unique_minimum hB
      (by change (0:ℝ)<1/2; norm_num) (by change (1:ℝ)/2<1; norm_num)
  have hz := minAt_zero_null_of_cyclic_prefix hclosed (bridgePath_law_cyclic hB) hp
  have hn : ∀ᵐ f ∂ν, f ∉ minAtSet 0 := (ae_iff.mpr (by simpa using hz))
  exact ae_of_ae_map (bridgePath_aemeasurable hB) hn

def innerCut (n : ℕ) : unitInterval :=
  ⟨1-(reciprocalTime n:ℝ),sub_nonneg.mpr (reciprocalTime n).property.2,
    sub_le_self _ (reciprocalTime n).property.1⟩

lemma innerCut_pos (n : ℕ) : 0 < innerCut n := by
  change (0:ℝ)<1-(reciprocalTime n:ℝ)
  linarith [reciprocalTime_le_half n]

lemma innerCut_lt_one (n : ℕ) : innerCut n < 1 := by
  change 1-1/((n:ℝ)+2)<(1:ℝ)
  have : (0:ℝ)<1/((n:ℝ)+2) := by positivity
  linarith

lemma exists_lt_innerCut {t : unitInterval} (ht : t < 1) : ∃ n, t < innerCut n := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (show (t:ℝ)<1 from ht))
  have hh : 1/((n:ℝ)+2)≤1/((n:ℝ)+1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  refine ⟨n,?_⟩
  change (t:ℝ)<1-1/((n:ℝ)+2)
  linarith

theorem bridge_unique_minimum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ c : unitInterval, 0<c ∧ c<1 ∧ UniqueMinimum (bridgePath B ω) c := by
  have hp : ∀ᵐ ω ∂P, ∀ n : ℕ, HasUniqueMinimum (prefixTimePath (innerCut n) (bridgePath B ω)) :=
    ae_all_iff.mpr fun n => bridge_prefix_unique_minimum hB (innerCut_pos n) (innerCut_lt_one n)
  filter_upwards [hp,bridge_not_minimum_zero hB,bridgePath_closed hB] with ω hprefix hzero hclosed
  let f := bridgePath B ω
  let c := minTime f
  have hc := minTime_spec f
  have hcz : c ≠ 0 := by intro he; exact hzero (by simpa only [← he] using hc)
  have hco : c ≠ 1 := by
    intro he
    apply hzero
    intro t
    calc f 0=f 1 := hclosed.1.trans hclosed.2.symm
         _=f c := by rw [he]
         _≤f t := hc t
  have hc₀ : 0<c := lt_of_le_of_ne (by exact c.property.1) (Ne.symm hcz)
  have hc₁ : c<1 := lt_of_le_of_ne (by exact c.property.2) hco
  refine ⟨c,hc₀,hc₁,hc,?_⟩
  intro t ht
  have htmin : ∀ s, f t ≤ f s := fun s => ht.trans_le (hc s)
  have hto : t ≠ 1 := by
    intro he
    apply hzero
    intro s
    calc f 0=f 1 := hclosed.1.trans hclosed.2.symm
         _=f t := by rw [he]
         _≤f s := htmin s
  have ht₁ : t<1 := lt_of_le_of_ne t.property.2 hto
  obtain ⟨n,hn⟩ := exists_lt_innerCut (max_lt ht₁ hc₁)
  exact eq_of_minima_in_unique_prefix (innerCut_pos n) (hprefix n) htmin hc
    ((le_max_left t c).trans hn.le) ((le_max_right t c).trans hn.le)

theorem probabilityMeasure_tendsto_map_aeContinuous {E F ι : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {l : Filter ι} [l.IsCountablyGenerated] {ν : ι → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} {g : E → F} (hg : Measurable g)
    (h : Tendsto ν l (𝓝 μ)) (hcont : ∀ᵐ x ∂(μ:Measure E), ContinuousAt g x) :
    Tendsto (fun n => (ν n).map g) l (𝓝 (μ.map g)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro K hK
  have he : (μ:Measure E) (closure (g ⁻¹' K))=(μ:Measure E) (g ⁻¹' K) := by
    apply measure_congr
    filter_upwards [hcont] with x hx
    apply propext
    constructor
    · intro hmem
      have hh := mem_closure_image hx hmem
      exact hK.closure_eq ▸ (closure_mono (image_preimage_subset g K) hh)
    · intro hx; exact subset_closure hx
  have hle : (fun n => ((ν n).map g : Measure F) K) ≤
      (fun n => (ν n:Measure E) (closure (g ⁻¹' K))) := by
    intro n
    change ((ν n:Measure E).map g) K≤_
    rw [Measure.map_apply hg hK.measurableSet]
    exact measure_mono subset_closure
  have hh := (Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)).trans
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h isClosed_closure)
  rw [he] at hh
  change _≤((μ:Measure E).map g) K
  rw [Measure.map_apply hg hK.measurableSet]
  exact hh

theorem TendstoInDistribution.aeContinuous_comp {E F ι Ω' : Type*} {Ω : ι → Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {l : Filter ι} [l.IsCountablyGenerated] {X : (n : ι) → Ω n → E} {Z : Ω' → E}
    {P : (n : ι) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {g : E → F}
    (hg : Measurable g) (h : TendstoInDistribution X l Z P Q)
    (hcont : ∀ᵐ x ∂Q.map Z, ContinuousAt g x) :
    TendstoInDistribution (fun n => g ∘ X n) l (g ∘ Z) P Q where
  forall_aemeasurable n := hg.comp_aemeasurable (h.forall_aemeasurable n)
  aemeasurable_limit := hg.comp_aemeasurable h.aemeasurable_limit
  tendsto := by
    have hh := probabilityMeasure_tendsto_map_aeContinuous hg h.tendsto hcont
    have hn (n : ι) :
        ProbabilityMeasure.map (⟨(P n).map (X n),inferInstance⟩ :
          ProbabilityMeasure E) g =
        (⟨(P n).map (g ∘ X n),inferInstance⟩ : ProbabilityMeasure F) := by
      apply Subtype.ext
      exact AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (h.forall_aemeasurable n)
    have hz :
        ProbabilityMeasure.map (⟨Q.map Z,inferInstance⟩ :
          ProbabilityMeasure E) g =
        (⟨Q.map (g ∘ Z),inferInstance⟩ : ProbabilityMeasure F) := by
      apply Subtype.ext
      exact AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h.aemeasurable_limit
    simpa only [hn,hz] using hh

theorem CriticalEvenOffspring.iidVervaat_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    TendstoInDistribution (fun n d => vervaat (p.iidWalk (2*n+1) d)) atTop
      (fun ω => vervaat (bridgePath B ω)) p.iidBridgeLaw P := by
  apply TendstoInDistribution.aeContinuous_comp measurable_vervaat (p.iidBridge_CLT hB)
  have hp : ∀ᵐ f ∂P.map (bridgePath B), HasUniqueMinimum f := by
    apply (ae_map_iff (bridgePath_aemeasurable hB) measurableSet_hasUniqueMinimum).mpr
    filter_upwards [bridge_unique_minimum hB] with ω hω
    obtain ⟨c,_,_,hc⟩ := hω
    exact ⟨c,hc⟩
  filter_upwards [hp] with f hf
  obtain ⟨c,hc⟩ := hf
  exact continuousAt_vervaat hc

end FKCRT.TreeCoding
end

end OAI
