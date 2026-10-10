import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.GaugeBounds
import OAI.Probability.SLEGauge.InitialTrace
import OAI.Probability.SLEGauge.AngleGenerators

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerScaling
open ExactSLEMain ExactSLEGreen

 
def scaled (c : ℝ≥0) (b : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (c : ℝ)⁻¹ * b (c^2*t)

@[simp] lemma scaled_scaled {c : ℝ≥0} (hc : c≠0) (b : ℝ≥0 → ℝ) :
    scaled c⁻¹ (scaled c b)=b := by
  ext t
  simp only [scaled, NNReal.coe_inv, inv_inv, inv_pow]
  have htime : c^2*(c^2)⁻¹*t=t := by rw [mul_inv_cancel₀ (pow_ne_zero _ hc),one_mul]
  simp only [←mul_assoc,htime,mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hc),one_mul]

lemma scaled_continuous (c : ℝ≥0) {b : ℝ≥0 → ℝ} (hb : Continuous b) :
    Continuous (scaled c b) := continuous_const.mul (hb.comp (continuous_const.mul continuous_id))

 
def scaleDriver (c : ℝ≥0) (b : ExactSLEGenerator.Driver) : ExactSLEGenerator.Driver :=
  ⟨⟨scaled c b.1,scaled_continuous c b.1.continuous⟩,by simp [scaled,b.2]⟩

@[simp] lemma scaleDriver_apply (c : ℝ≥0) (b : ExactSLEGenerator.Driver) (t : ℝ≥0) :
    (scaleDriver c b).1 t=(c:ℝ)⁻¹*b.1 (c^2*t) := rfl

@[simp] lemma scaleDriver_inv {c : ℝ≥0} (hc : c≠0) (b : ExactSLEGenerator.Driver) :
    scaleDriver c⁻¹ (scaleDriver c b)=b := by
  apply Subtype.ext
  apply ContinuousMap.ext
  exact congrFun (scaled_scaled hc b.1)

lemma continuous_scaleDriver (c : ℝ≥0) : Continuous (scaleDriver c) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ExactSLEGenerator.Driver × ℝ≥0 =>
    (c:ℝ)⁻¹*p.1.1 (c^2*p.2))
  exact continuous_const.mul (continuous_eval.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_const.mul continuous_snd)))

lemma odeUntil_scaled {a : ℝ} {c : ℝ≥0} (hc : 0<c)
    {b : ℝ≥0 → ℝ} {z : ℂ} {t : ℝ≥0} {f : ℝ → ℂ}
    (hf : odeUntil a b (((c:ℝ):ℂ)*z) (c^2*t) f) :
    odeUntil a (scaled c b) z t (fun u => ((c:ℝ):ℂ)⁻¹*f ((c:ℝ)^2*u)) := by
  have hcR : 0<(c:ℝ) := hc
  have hcC : ((c:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hcR.ne'
  refine ⟨?_,fun u hu => ?_⟩
  · simp only [mul_zero,hf.1,←mul_assoc,inv_mul_cancel₀ hcC,one_mul]
  have hmaps : MapsTo (fun u : ℝ => (c:ℝ)^2*u) (Icc 0 (t:ℝ))
      (Icc 0 ((c^2*t:ℝ≥0):ℝ)) := by
    intro v hv
    simp only [NNReal.coe_mul,NNReal.coe_pow,mem_Icc]
    exact ⟨mul_nonneg (sq_nonneg _) hv.1,mul_le_mul_of_nonneg_left hv.2 (sq_nonneg _)⟩
  have hnn : ((c:ℝ)^2*u).toNNReal=c^2*u.toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul,NNReal.coe_pow,
      Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) hu.1),Real.coe_toNNReal _ hu.1]
  constructor
  · simpa [←Complex.ofReal_inv,Complex.mul_im] using
      mul_pos (inv_pos.mpr hcR) (hf.2 _ (hmaps hu)).1
  · have hd := (hf.2 _ (hmaps hu)).2.scomp u
      ((hasDerivAt_id u).const_mul ((c:ℝ)^2)).hasDerivWithinAt hmaps
    have hd' := hd.const_mul ((c:ℝ):ℂ)⁻¹
    convert! hd' using 1
    change (a:ℂ) / (((c:ℝ):ℂ)⁻¹*f ((c:ℝ)^2*u) -
      (((c:ℝ)⁻¹*b (c^2*u.toNNReal):ℝ):ℂ)) = _
    rw [hnn]
    simp only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.real_smul,Complex.ofReal_pow]
    field_simp
    norm_num

lemma alive_scaled_iff (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    (b : ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) :
    alive a (scaled c b) t z ↔ alive a b (c^2*t) (((c:ℝ):ℂ)*z) := by
  constructor
  · rintro ⟨f,hf⟩
    have hct : (c⁻¹)^2*(c^2*t)=t := by simp [hc.ne']
    have hcz : (((c⁻¹:ℝ≥0):ℝ):ℂ)*(((c:ℝ):ℂ)*z)=z := by
      simp [hc.ne']
    have hs := odeUntil_scaled (inv_pos.mpr hc)
      (by rw [hct,hcz]; exact hf : odeUntil a (scaled c b)
        ((((c⁻¹:ℝ≥0):ℝ):ℂ)*(((c:ℝ):ℂ)*z)) ((c⁻¹)^2*(c^2*t)) f)
    rw [scaled_scaled hc.ne'] at hs
    exact ⟨_,hs⟩
  · rintro ⟨f,hf⟩
    exact ⟨_,odeUntil_scaled hc hf⟩

 

lemma loewnerMap_scaled (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    (b : ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) :
    loewnerMap a (scaled c b) t z =
      ((c:ℝ):ℂ)⁻¹*loewnerMap a b (c^2*t) (((c:ℝ):ℂ)*z) := by
  by_cases h : alive a b (c^2*t) (((c:ℝ):ℂ)*z)
  · obtain ⟨f,hf⟩ := h
    rw [loewnerMap_eq (odeUntil_scaled hc hf),loewnerMap_eq hf]
    simp only [NNReal.coe_mul,NNReal.coe_pow]
  · have hs := (alive_scaled_iff a hc b t z).not.mpr h
    simp only [loewnerMap,dite_eq_right h,dite_eq_right hs,mul_zero]

lemma deriv_loewnerMap_scaled (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) (t : ℝ≥0) (z : ℂ)
    (hz : alive a (scaled c b) t z) :
    deriv (loewnerMap a (scaled c b) t) z =
      deriv (loewnerMap a b (c^2*t)) (((c:ℝ):ℂ)*z) := by
  have h := (alive_scaled_iff a hc b t z).mp hz
  have hder := ((hasDerivAt_loewnerMap hb h).comp z
    ((hasDerivAt_id z).const_mul ((c:ℝ):ℂ))).const_mul ((c:ℝ):ℂ)⁻¹
  have hf : (fun w => ((c:ℝ):ℂ)⁻¹*
      (loewnerMap a b (c^2*t) ∘ fun w => ((c:ℝ):ℂ)*w) w) =
      loewnerMap a (scaled c b) t := by
    funext w
    exact (loewnerMap_scaled a hc b t w).symm
  rw [hf] at hder
  rw [hder.deriv,(hasDerivAt_loewnerMap hb h).deriv]
  simp only [mul_one]
  field_simp [Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hc.ne')]

lemma actualState_scaled (a : ℝ) {c : ℝ≥0} (hc : 0<c)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) (t : ℝ≥0) (z : ℂ)
    (hz : alive a (scaled c b) t z) :
    actualState a (scaled c b) t z =
      (((c:ℝ):ℂ)⁻¹*(actualState a b (c^2*t) (((c:ℝ):ℂ)*z)).1,
       (actualState a b (c^2*t) (((c:ℝ):ℂ)*z)).2) := by
  apply Prod.ext
  · simp only [actualState,loewnerMap_scaled a hc,scaled,
      Complex.ofReal_mul,Complex.ofReal_inv,mul_sub]
  · simp only [actualState,deriv_loewnerMap_scaled a hc hb t z hz]

end SLEExactGauge.LoewnerScaling
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal ContinuousMapZero
namespace SLEExactGauge.FlowIdentification

abbrev TDriver := Target.Driver
abbrev GDriver := ExactSLEGenerator.Driver

 
def driverHomeomorph : TDriver ≃ₜ GDriver where
  toFun b := ⟨(b : C(ℝ≥0,ℝ)),map_zero b⟩
  invFun b := ⟨b.1,b.2⟩
  left_inv b := by ext t; rfl
  right_inv b := by ext t; rfl
  continuous_toFun := ContinuousMapZero.isEmbedding_toContinuousMap.continuous.subtype_mk _
  continuous_invFun := ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff.mpr
    continuous_subtype_val

@[simp] lemma driverHomeomorph_apply (b : TDriver) (t : ℝ≥0) :
    (driverHomeomorph b).1 t=b t := rfl

@[simp] lemma driverHomeomorph_symm_apply (b : GDriver) (t : ℝ≥0) :
    driverHomeomorph.symm b t=b.1 t := rfl

lemma measurable_driverHomeomorph : Measurable driverHomeomorph :=
  driverHomeomorph.continuous.measurable

lemma measurable_driverHomeomorph_symm : Measurable driverHomeomorph.symm :=
  driverHomeomorph.symm.continuous.measurable

def driverMeasurableEquiv : TDriver ≃ᵐ GDriver :=
  ⟨driverHomeomorph.toEquiv, measurable_driverHomeomorph,measurable_driverHomeomorph_symm⟩

lemma brownian_map_driver (W : Measure TDriver) (hW : Target.IsWiener W) :
    IsBrownianReal (fun t (b : GDriver) => b.1 t) (W.map driverHomeomorph) where
  hasLaw I := by
    refine ⟨(Measurable.of_eval (fun t : I =>
      (ExactSLEGenerator.driver_eval_measurable t).measurable)).aemeasurable,?_⟩
    change (W.map driverHomeomorph).map (fun b : GDriver => fun t : I => b.1 t)=_
    rw [Measure.map_map (Measurable.of_eval (fun t : I =>
      (ExactSLEGenerator.driver_eval_measurable t).measurable)) measurable_driverHomeomorph]
    exact (hW.hasLaw I).map_eq
  cont := Eventually.of_forall (fun b => b.1.continuous)

lemma positiveSolution_iff (κ : ℝ) (b : TDriver) (z : ℂ) (t : ℝ≥0) (f : ℝ → ℂ) :
    LiteralTrace.PositiveSolution κ b z t f ↔
      ExactSLEMain.odeUntil (Target.a κ) (driverHomeomorph b).1 z t f := by
  constructor
  · intro hf
    exact ⟨hf.2.2.1,fun u hu => ⟨hf.2.2.2.1 u hu,hf.2.2.2.2 u hu⟩⟩
  · intro hf
    exact ⟨t.coe_nonneg,ExactSLEMain.odeUntil_continuousOn hf,hf.1,
      fun u hu => (hf.2 u hu).1,fun u hu => (hf.2 u hu).2⟩

lemma eulerSteps_eq (κ : ℝ) (b : TDriver) (j N : ℕ) (z : ℂ) (k : ℕ) :
    Target.eulerSteps κ b j N z k=LiteralTrace.eulerSteps κ b j N z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Target.eulerSteps,LiteralTrace.eulerSteps,ih]
    rfl

lemma eulerFlow_eq (κ : ℝ) (b : TDriver) (j N : ℕ) (z : ℂ) (t : ℝ) :
    Target.eulerFlow κ b j N z t=LiteralTrace.eulerFlow κ b j N z t := by
  simp only [Target.eulerFlow,LiteralTrace.eulerFlow,eulerSteps_eq]
  rfl

lemma cutoffFlow_eq (κ : ℝ) (b : TDriver) (j : ℕ) (z : ℂ) (t : ℝ) :
    Target.cutoffFlow κ b j z t=LiteralTrace.cutoffFlow κ b j z t := by
  simp only [Target.cutoffFlow,LiteralTrace.cutoffFlow,eulerFlow_eq]

lemma surviving_eq (κ : ℝ) (b : TDriver) (z : ℂ) (t : ℝ) :
    Target.Surviving κ b z t = LiteralTrace.Surviving κ b z t := by
  simp only [Target.Surviving,LiteralTrace.Surviving,cutoffFlow_eq]

lemma surviving_iff_alive (κ : ℝ) (b : TDriver) (z : ℂ) (t : ℝ≥0) :
    Target.Surviving κ b z t ↔ ExactSLEMain.alive (Target.a κ) (driverHomeomorph b).1 t z := by
  rw [surviving_eq,LiteralTrace.surviving_iff_positiveSolution t.coe_nonneg]
  exact exists_congr (positiveSolution_iff κ b z t)

lemma flow_eq_literal (κ : ℝ) (b : TDriver) (z : ℂ) (t : ℝ) :
    Target.flow κ b z t=LiteralTrace.flow κ b z t := by
  classical
  unfold Target.flow LiteralTrace.flow
  split_ifs with ht hl hl
  · have he : Nat.find ht=Nat.find hl := by
      apply le_antisymm
      · apply Nat.find_min' ht
        simpa only [cutoffFlow_eq] using Nat.find_spec hl
      · apply Nat.find_min' hl
        simpa only [cutoffFlow_eq] using Nat.find_spec ht
    rw [he,cutoffFlow_eq]
  · exact False.elim (hl ((surviving_eq κ b z t).mp ht))
  · exact False.elim (ht ((surviving_eq κ b z t).mpr hl))
  · rfl

lemma flow_eq_loewnerMap (κ : ℝ) (b : TDriver) (z : ℂ) (t : ℝ≥0) :
    Target.flow κ b z t=ExactSLEMain.loewnerMap (Target.a κ) (driverHomeomorph b).1 t z := by
  by_cases ht : Target.Surviving κ b z t
  · have ht' : LiteralTrace.Surviving κ b z t := (surviving_eq κ b z t).mp ht
    have hp := LiteralTrace.surviving_flow_positiveSolution t.coe_nonneg ht'
    rw [flow_eq_literal]
    exact (ExactSLEMain.loewnerMap_eq ((positiveSolution_iff κ b z t _).mp hp)).symm
  · have hn : ¬ExactSLEMain.alive (Target.a κ) (driverHomeomorph b).1 t z :=
      fun h => ht ((surviving_iff_alive κ b z t).mpr h)
    simp [Target.flow,ExactSLEMain.loewnerMap,ht,hn]

lemma flow_eq_loewnerMap_real (κ : ℝ) (b : TDriver) (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    Target.flow κ b z t=ExactSLEMain.loewnerMap (Target.a κ) (driverHomeomorph b).1 t.toNNReal z := by
  simpa only [Real.coe_toNNReal _ ht] using flow_eq_loewnerMap κ b z t.toNNReal

lemma inverseFlow_eq_literal (κ : ℝ) (b : TDriver) (t : ℝ) (w : ℂ) :
    Target.inverseFlow κ b t w=LiteralTrace.inverseFlow κ b t w := by
  classical
  have he : (fun z : ℂ => Target.Surviving κ b z t ∧ Target.flow κ b z t=w)=
      (fun z : ℂ => LiteralTrace.Surviving κ b z t ∧ LiteralTrace.flow κ b z t=w) := by
    funext z
    rw [surviving_eq,flow_eq_literal]
  unfold Target.inverseFlow LiteralTrace.inverseFlow
  rw [he]

lemma trace_eq_literal (κ : ℝ) (b : TDriver) :
    Target.trace κ b=LiteralTrace.trace κ b := by
  funext t
  simp only [Target.trace,LiteralTrace.trace,inverseFlow_eq_literal]
  rfl

 

theorem trace_regular_actual_domains {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {W : Measure TDriver} (hW : Target.IsWiener W) :
    ∀ᵐ b ∂W,
      ContinuousOn (Target.trace κ b) (Ici 0) ∧
      (∀ t : ℝ, 0 ≤ t → Target.trace κ b t ∈
        frontier {z | ExactSLEMain.alive (Target.a κ) (driverHomeomorph b).1 (κ*t).toNNReal z}) ∧
      (∀ s : ℝ, 0 ≤ s → (Target.trace κ b) '' Ici s ⊆
        closure {z | ExactSLEMain.alive (Target.a κ) (driverHomeomorph b).1 (κ*s).toNNReal z}) := by
  have hdomain (b : TDriver) (t : ℝ) (ht : 0 ≤ t) :
      {z | LiteralTrace.Surviving κ b z (κ*t)}=
        {z | ExactSLEMain.alive (Target.a κ) (driverHomeomorph b).1 (κ*t).toNNReal z} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    simpa only [surviving_eq,Real.coe_toNNReal _ (mul_nonneg hκ.le ht)] using
      surviving_iff_alive κ b z (κ*t).toNNReal
  filter_upwards [LiteralTrace.trace_regular_all_times hκ hκ8 hW] with b hb
  simp only [trace_eq_literal]
  refine ⟨hb.2.1,?_,?_⟩
  · intro t ht
    rw [←hdomain b t ht]
    exact hb.2.2.1 t ht
  · intro s hs
    rw [←hdomain b s hs]
    exact hb.2.2.2 s hs

end SLEExactGauge.FlowIdentification
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerScaling
open FlowIdentification

lemma brownian_map_inverse_driver (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W) :
    Target.IsWiener (W.map driverHomeomorph.symm) where
  hasLaw I := by
    refine ⟨(Measurable.of_eval (fun t : I =>
      (continuous_eval_const (t:ℝ≥0)).measurable)).aemeasurable,?_⟩
    change (W.map driverHomeomorph.symm).map
      (fun b : TDriver => fun t : I => b t)=_
    rw [Measure.map_map (Measurable.of_eval (fun t : I =>
      (continuous_eval_const (t:ℝ≥0)).measurable)) measurable_driverHomeomorph_symm]
    exact (hW.hasLaw I).map_eq
  cont := Eventually.of_forall (fun b => b.continuous)

lemma brownian_evaluation_law_unique {W V : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (hV : IsBrownianReal (fun t (b : GDriver) => b.1 t) V) : W=V := by
  apply driverMeasurableEquiv.symm.measurableEmbedding.map_injective
  exact BrownianLaw.evaluation_law_unique (brownian_map_inverse_driver W hW)
    (brownian_map_inverse_driver V hV)

lemma brownian_scaled {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {c : ℝ≥0} (hc : 0<c) :
    IsBrownianReal (fun t (b : GDriver) => (scaleDriver c b).1 t) W := by
  simpa [scaleDriver_apply,Real.sqrt_sq c.coe_nonneg] using hW.smul (pow_ne_zero 2 hc.ne')

lemma brownian_map_scaled {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {c : ℝ≥0} (hc : 0<c) :
    IsBrownianReal (fun t (b : GDriver) => b.1 t) (W.map (scaleDriver c)) where
  hasLaw I := by
    refine ⟨(Measurable.of_eval (fun t : I =>
      (ExactSLEGenerator.driver_eval_measurable t).measurable)).aemeasurable,?_⟩
    change (W.map (scaleDriver c)).map (fun b : GDriver => fun t : I => b.1 t)=_
    rw [Measure.map_map (Measurable.of_eval (fun t : I =>
      (ExactSLEGenerator.driver_eval_measurable t).measurable)) (continuous_scaleDriver c).measurable]
    exact ((brownian_scaled hW hc).hasLaw I).map_eq
  cont := Eventually.of_forall (fun b => b.1.continuous)

lemma map_scaleDriver_eq {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {c : ℝ≥0} (hc : 0<c) : W.map (scaleDriver c)=W :=
  brownian_evaluation_law_unique (brownian_map_scaled hW hc) hW

lemma measurePreserving_scaleDriver {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {c : ℝ≥0} (hc : 0<c) : MeasurePreserving (scaleDriver c) W W :=
  ⟨(continuous_scaleDriver c).measurable,map_scaleDriver_eq hW hc⟩

end SLEExactGauge.LoewnerScaling
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace ExactSLEMain

lemma odeUntil_join {a : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {s t : ℝ≥0}
    {f g : ℝ → ℂ} (hf : odeUntil a b z s f)
    (hg : odeUntil a (shiftDriver b s) (f s - (b s : ℂ)) t g) :
    odeUntil a b z (s+t) (fun u => if u ≤ s then f u else g (u-s)+(b s : ℂ)) := by
  classical
  let k : ℝ → ℂ := fun u => if u ≤ s then f u else g (u-s)+(b s : ℂ)
  have hk₁ : EqOn k f (Icc 0 (s:ℝ)) := fun u hu => ite_eq_left hu.2
  have hk₂ : EqOn k (fun u => g (u-s)+(b s : ℂ)) (Icc (s:ℝ) (s+t)) := by
    intro u hu
    dsimp only [k]
    split_ifs with h
    · have he : u=(s:ℝ) := le_antisymm h hu.1
      simp only [he,sub_self,hg.1,sub_add_cancel]
    · rfl
  have hmaps : MapsTo (fun u : ℝ => u-s) (Icc (s:ℝ) (s+t)) (Icc 0 (t:ℝ)) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2]
  have hd₁ (u : ℝ) (hu : u ∈ Icc 0 (s:ℝ)) :
      HasDerivWithinAt k ((a:ℂ)/(k u-(b u.toNNReal:ℂ))) (Icc 0 (s:ℝ)) u := by
    rw [hk₁ hu]
    exact (hf.2 u hu).2.congr_of_mem hk₁ hu
  have hd₂ (u : ℝ) (hu : u ∈ Icc (s:ℝ) (s+t)) :
      HasDerivWithinAt k ((a:ℂ)/(k u-(b u.toNNReal:ℂ))) (Icc (s:ℝ) (s+t)) u := by
    have hnn : s+(u-(s:ℝ)).toNNReal=u.toNNReal := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add,Real.coe_toNNReal _ (sub_nonneg.mpr hu.1),
        Real.coe_toNNReal _ (s.coe_nonneg.trans hu.1)]
      ring
    have h := ((hg.2 _ (hmaps hu)).2.scomp u
      ((hasDerivAt_id u).sub_const (s:ℝ)).hasDerivWithinAt hmaps).add_const (b s:ℂ)
    simp only [one_smul,shiftDriver,hnn,Complex.ofReal_sub] at h
    rw [hk₂ hu]
    convert h.congr_of_mem hk₂ hu using 1; congr 1; ring
  refine ⟨by change k 0=z; rw [hk₁ (by simp),hf.1],fun u hu => ?_⟩
  have hu' : u ∈ Icc 0 ((s:ℝ)+t) := hu
  change 0<(k u).im ∧ HasDerivWithinAt k _ _ u
  constructor
  · by_cases hs : u≤(s:ℝ)
    · rw [hk₁ ⟨hu.1,hs⟩]
      exact (hf.2 u ⟨hu.1,hs⟩).1
    · have hu₂ : u ∈ Icc (s:ℝ) (s+t) := ⟨(le_of_not_ge hs),hu.2⟩
      rw [hk₂ hu₂]
      simpa only [Complex.add_im,Complex.ofReal_im,add_zero] using (hg.2 _ (hmaps hu₂)).1
  · rcases lt_trichotomy u (s:ℝ) with hs | hs | hs
    · apply (hd₁ u ⟨hu.1,hs.le⟩).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hs)] with v hv hvs
      exact ⟨hv.1,hvs.le⟩
    · subst u
      have h := (hd₁ (s:ℝ) ⟨s.coe_nonneg,le_rfl⟩).union
        (hd₂ (s:ℝ) ⟨le_rfl,le_add_of_nonneg_right t.coe_nonneg⟩)
      rw [Icc_union_Icc_eq_Icc s.coe_nonneg (le_add_of_nonneg_right t.coe_nonneg)] at h
      exact h
    · apply (hd₂ u ⟨hs.le,hu.2⟩).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds hs)] with v hv hsv
      exact ⟨hsv.le,hv.2⟩

 
theorem alive_restart_iff (a : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (s t : ℝ≥0) :
    alive a b (s+t) z ↔ alive a b s z ∧
      alive a (shiftDriver b s) t (loewnerMap a b s z-(b s:ℂ)) := by
  constructor
  · intro h
    exact ⟨alive_mono h (by exact le_add_of_nonneg_right bot_le),
      (loewnerMap_restart a b z s t h).1⟩
  · rintro ⟨⟨f,hf⟩,g,hg⟩
    rw [loewnerMap_eq hf] at hg
    exact ⟨_,odeUntil_join hf hg⟩

lemma continuous_shiftDriver {b : ℝ≥0 → ℝ} (hb : Continuous b) (s : ℝ≥0) :
    Continuous (shiftDriver b s) :=
  (hb.comp (continuous_const.add continuous_id)).sub continuous_const

 

lemma deriv_loewnerMap_restart {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {s t : ℝ≥0} (hz : alive a b (s+t) z) :
    deriv (loewnerMap a b (s+t)) z =
      deriv (loewnerMap a (shiftDriver b s) t) (loewnerMap a b s z-(b s:ℂ)) *
        deriv (loewnerMap a b s) z := by
  have hs := (alive_restart_iff a b z s t).mp hz
  have hd := ((hasDerivAt_loewnerMap (continuous_shiftDriver hb s) hs.2).comp z
    ((hasDerivAt_loewnerMap hb hs.1).sub_const (b s:ℂ))).add_const (b s:ℂ)
  have he : (fun w => loewnerMap a (shiftDriver b s) t (loewnerMap a b s w-(b s:ℂ))+(b s:ℂ))
      =ᶠ[𝓝 z] loewnerMap a b (s+t) := by
    filter_upwards [(isOpen_alive hb (s+t)).mem_nhds hz] with w hw
    rw [(loewnerMap_restart a b w s t hw).2,sub_add_cancel]
  rw [(hd.congr_of_eventuallyEq he.symm).deriv,
    (hasDerivAt_loewnerMap hb hs.1).deriv,
    (hasDerivAt_loewnerMap (continuous_shiftDriver hb s) hs.2).deriv]

end ExactSLEMain
end
end

end OAI
