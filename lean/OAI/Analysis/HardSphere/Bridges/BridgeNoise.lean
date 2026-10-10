import Mathlib
import OAI.Analysis.HardSphere.Bridges.GaussianMixture
import OAI.Analysis.HardSphere.Bridges.BridgeMoment

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def fluctuation (t r : ℝ) (u : Time) (β : Noise) : ℝ := Real.sqrt (2*t)/r*prefixSize u β
lemma fluctuation_continuous (t r : ℝ) (u : Time) : Continuous (fluctuation t r u) :=
  (prefixSize_continuous u).const_mul _
lemma fluctuation_nonneg {t r : ℝ} (hr : 0≤r) (u : Time) (β : Noise) : 0≤fluctuation t r u β :=
  mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hr) (prefixSize_nonneg u β)
lemma fluctuation_memLp (t r : ℝ) (s u : Time) : MemLp (fluctuation t r u) 3 (law.map (remainder s)) :=
  (remainder_prefix_memLp s u).const_mul _

lemma fluctuation_mean {t r : ℝ} (ht : 0≤t) (hr : 0<r) (s u : Time)
    (hscale : t*(1-(s:ℝ))*(u:ℝ)≤r^2) :
    ∫β,(fluctuation t r u β)^3 ∂law.map (remainder s) ≤ 3072*normCubeMean := by
  let a := Real.sqrt (2*t)/r*Real.sqrt (1-(s:ℝ))*Real.sqrt (u:ℝ)
  have ha0 : 0≤a := by dsimp [a]; positivity
  have ha2 : a^2≤2 := by
    dsimp [a]
    rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (sub_nonneg.mpr s.property.2),Real.sq_sqrt u.property.1]
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    convert mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ)≤2) using 1
    ring
  have ha : a≤2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left (remainder_prefix_mean s u)
    (show 0≤(Real.sqrt (2*t)/r)^3 by positivity)
  simp only [fluctuation,mul_pow,integral_const_mul]
  calc
    _ ≤ _ := hb
    _ = 384*a^3*normCubeMean := by dsimp [a]; ring
    _ ≤ 3072*normCubeMean := by
      have hc := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 ha 3) normCubeMean_nonneg
      nlinarith

lemma prefix_norm_eval (u q : Time) (hq : (q:ℝ)≤(u:ℝ)) (β : C(Time,ℝ)) :
    ‖β q‖≤‖prefixMap u β‖ := by
  by_cases hu : (u:ℝ)=0
  · have hq0 : (q:ℝ)=0 := le_antisymm (hq.trans_eq hu) q.property.1
    have he : prefixTime u 0=q := Subtype.ext (by simp [prefixTime,hq0])
    simpa only [prefixMap_apply,he] using ContinuousMap.norm_coe_le_norm (prefixMap u β) 0
  · have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm hu)
    let z : Time := ⟨(q:ℝ)/(u:ℝ),div_nonneg q.property.1 u.property.1,(div_le_one hup).mpr hq⟩
    have he : prefixTime u z=q := by apply Subtype.ext; dsimp [prefixTime,z]; field_simp
    simpa only [prefixMap_apply,he] using ContinuousMap.norm_coe_le_norm (prefixMap u β) z

lemma fluctuation_eval {t r : ℝ} (hr : 0<r) (u q : Time) (hq : (q:ℝ)≤(u:ℝ)) (β : Noise) (j : Fin 3) :
    |Real.sqrt (2*t)*β j q|≤r*fluctuation t r u β := by
  have hp : ‖β j q‖≤prefixSize u β := (prefix_norm_eval u q hq (β j)).trans
    (Finset.single_le_sum (fun i _ ↦ norm_nonneg (prefixMap u (β i))) (Finset.mem_univ j))
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  have he : r*fluctuation t r u β=Real.sqrt (2*t)*prefixSize u β := by unfold fluctuation; field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma cube_volume (q : Point) {δ : ℝ} (hδ : 0≤δ) :
    (volume : Measure Point) (cube q δ)=ENNReal.ofReal ((2*δ)^3) := by
  rw [←cube_real_volume q hδ,Measure.real,ENNReal.ofReal_toReal]
  exact (IsCompact.measure_lt_top isCompact_Icc).ne

lemma measurable_cube_event {Ω : Type*} [MeasurableSpace Ω] {R : Ω → ℝ}
    (hR : Measurable R) (c : Point) (r A : ℝ) :
    MeasurableSet {p : Ω×Point | p.2∈cube c (r*(A+R p.1))} := by
  apply Measurable.setOf
  have hm (j : Fin 3) : Measurable (fun p : Ω×Point ↦ p.2 j) := (measurable_pi_apply j).comp measurable_snd
  exact (Measurable.forall fun j ↦ (measurableSet_le (measurable_const.sub
    ((hR.comp measurable_fst).const_add A |>.const_mul r)) (hm j)).mem).and
    (Measurable.forall fun j ↦ (measurableSet_le (hm j) (measurable_const.add
      ((hR.comp measurable_fst).const_add A |>.const_mul r))).mem)

theorem collision_volume_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ : Measure Point) [SFinite μ]
    {R : Ω → ℝ} (hR : Measurable R) (hR0 : ∀ω,0≤R ω) (hR3 : MemLp R 3 ν)
    (c : Point) {r A C : ℝ} (hr : 0≤r) (hA : 0≤A) (hC : 0≤C)
    (hμ : μ ≤ ENNReal.ofReal C • (volume : Measure Point)) :
    (ν.prod μ) {p : Ω×Point | p.2∈cube c (r*(A+R p.1))} ≤
      ENNReal.ofReal (8*C*r^3*(∫ω,(A+R ω)^3 ∂ν)) := by
  have hInt : Integrable (fun ω ↦ (A+R ω)^3) ν := by
    have h := ((memLp_const A).add hR3).integrable_norm_pow (by norm_num : (3:ℕ)≠0)
    simpa only [Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (add_nonneg hA (hR0 _))] using h
  rw [Measure.prod_apply (measurable_cube_event hR c r A)]
  calc
    _ ≤ ∫⁻ω,ENNReal.ofReal C*(volume : Measure Point) (cube c (r*(A+R ω))) ∂ν := by
      apply lintegral_mono
      intro ω
      exact hμ (cube c (r*(A+R ω)))
    _ = ∫⁻ω,ENNReal.ofReal (8*C*r^3*(A+R ω)^3) ∂ν := by
      apply lintegral_congr
      intro ω
      have hp : 0≤R ω := hR0 ω
      rw [cube_volume c (by positivity),←ENNReal.ofReal_mul hC]
      congr 1
      ring
    _ = _ := by
      rw [←ofReal_integral_eq_lintegral_ofReal (hInt.const_mul _)
        (Eventually.of_forall fun ω ↦ by have hp:=hR0 ω; positivity),integral_const_mul]

theorem collision_cubic_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ : Measure Point) [SFinite μ]
    {R : Ω → ℝ} (hR : Measurable R) (hR0 : ∀ω,0≤R ω) (hR3 : MemLp R 3 ν)
    (c : Point) {r A C : ℝ} (hr : 0≤r) (hA : 0≤A) (hC : 0≤C)
    (hμ : μ ≤ ENNReal.ofReal C • (volume : Measure Point)) :
    (ν.prod μ) {p : Ω×Point | p.2∈cube c (r*(A+R p.1))} ≤
      ENNReal.ofReal (32*C*r^3*(A^3+∫ω,(R ω)^3 ∂ν)) := by
  apply (collision_volume_bound ν μ hR hR0 hR3 c hr hA hC hμ).trans
  apply ENNReal.ofReal_le_ofReal
  have hInt0 : Integrable (fun ω ↦ (R ω)^3) ν := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hR0 _)] using hR3.integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  have hInt : Integrable (fun ω ↦ (A+R ω)^3) ν := by
    simpa only [Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (add_nonneg hA (hR0 _))] using
      ((memLp_const A).add hR3).integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  have hi : (∫ω,(A+R ω)^3 ∂ν) ≤ 4*(A^3+∫ω,R ω^3 ∂ν) := by
    have h := integral_mono hInt (((integrable_const (A^3)).add hInt0).const_mul 4)
      (fun ω ↦ Wiener.cube_add_le hA (hR0 ω))
    simpa only [Pi.add_apply,integral_const_mul,integral_add (integrable_const (A^3)) hInt0,
      integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using h
  nlinarith [mul_le_mul_of_nonneg_left hi (show 0≤8*C*r^3 by positivity)]

end HardSphere.GaussianPacking

end
end

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma leg_segment (t : ℝ) (y v : Point) (β : Noise) (s q : Time) (j : Fin 3) :
    leg t y v β (suffixTime s q) j=leg t y v β s j+
      (q:ℝ)*(v j-leg t y v β s j)+Real.sqrt (2*t)*remainder s β j q := by
  simp only [leg,ContinuousMap.coe_mk,mean,remainder,bridgeRemainder_apply]
  dsimp [suffixTime]
  ring

def segmentHit (t : ℝ) (y v : Point) (s w : Time) (c : Time → Point) (r C : ℝ) : Set Noise :=
  {β | ‖leg t y v β s-v‖≤C ∧ ∃q : Time,(q:ℝ)≤(w:ℝ) ∧ ‖leg t y v β (suffixTime s q)-c q‖≤r}

lemma segment_necessary {t r C A : ℝ} (hr : 0<r) (hC : 0≤C) (y v : Point) (s w : Time)
    (c : Time → Point) (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖≤r*A)
    (hdrift : (w:ℝ)*C≤r) : segmentHit t y v s w c r C ⊆
      {β | leg t y v β s ∈ cube (c 0) (r*(2+A+fluctuation t r w (remainder s β)))} := by
  rintro β ⟨hc,q,hq,hh⟩
  have hb (j : Fin 3) : |leg t y v β s j-c 0 j|≤r*(2+A+fluctuation t r w (remainder s β)) := by
    have hi : |leg t y v β (suffixTime s q) j-c q j|≤r := (norm_le_pi_norm _ j).trans hh
    have ho : |c q j-c 0 j|≤r*A := (norm_le_pi_norm _ j).trans (hA q hq)
    have hd : |(q:ℝ)*(v j-leg t y v β s j)|≤r := by
      rw [abs_mul,abs_of_nonneg q.property.1,abs_sub_comm]
      exact (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ j).trans hc) q.property.1).trans
        ((mul_le_mul_of_nonneg_right hq hC).trans hdrift)
    have hn := fluctuation_eval (t:=t) hr w q hq (remainder s β) j
    have he : leg t y v β s j-c 0 j=
        ((leg t y v β (suffixTime s q) j-c q j)+(c q j-c 0 j))-
        (q:ℝ)*(v j-leg t y v β s j)-Real.sqrt (2*t)*remainder s β j q := by rw [leg_segment]; ring
    rw [he]
    calc
      _ ≤ (|leg t y v β (suffixTime s q) j-c q j|+|c q j-c 0 j|)+
          |(q:ℝ)*(v j-leg t y v β s j)|+|Real.sqrt (2*t)*remainder s β j q| :=
        (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ (r+r*A)+r+r*fluctuation t r w (remainder s β) := by gcongr
      _ = _ := by ring
  exact ⟨fun j ↦ by have h := (abs_le.mp (hb j)).1; dsimp; linarith,
    fun j ↦ by have h := (abs_le.mp (hb j)).2; dsimp; linarith⟩

lemma segment_sum_bound {m : ℕ} (y : Fin m → Point) (v : Point) (s w : Time)
    (c : Time → Point) {t r C A ε : ℝ} (ht : 0<t) (hr : 0<r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)<1) (hε : 0<ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j))
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖≤r*A)
    (hdrift : (w:ℝ)*C≤r) (hscale : t*(1-(s:ℝ))*(w:ℝ)≤r^2) :
    (∑i,law (segmentHit t (y i) v s w c r C)) ≤
      ENNReal.ofReal (32*(packingConstant*(((1-(s:ℝ))*ε)⁻¹^3+
        (Real.sqrt ((2*(legVariance t s:ℝ))⁻¹))^3))*r^3*((2+A)^3+3072*normCubeMean)) := by
  let ν := law.map (remainder s)
  let μ (i : Fin m) := Measure.pi (fun j : Fin 3 ↦ gaussianReal (mean (y i) v s j) (legVariance t s))
  let R := fluctuation t r w
  let E := {p : Noise×Point | p.2∈cube (c 0) (r*((2+A)+R p.1))}
  have hE : MeasurableSet E := measurable_cube_event (fluctuation_continuous t r w).measurable (c 0) r (2+A)
  have : IsProbabilityMeasure ν := inferInstance
  have hu : (∑i,law (segmentHit t (y i) v s w c r C)) ≤ (ν.prod (∑i,μ i)) E := by
    rw [←Measure.sum_fintype,Measure.prod_sum_right,Measure.sum_fintype,Measure.finsetSum_apply]
    apply Finset.sum_le_sum
    intro i hi
    apply (measure_mono (segment_necessary hr hC (y i) v s w c hA hdrift)).trans_eq
    have he : {β | leg t (y i) v β s∈cube (c 0) (r*(2+A+R (remainder s β)))}=
        (fun β ↦ (remainder s β,leg t (y i) v β s))⁻¹' E := rfl
    rw [he,←Measure.map_apply ((remainder_measurable s).prodMk (leg_eval_measurable t (y i) v s)) hE,position_joint]
  have hμ := gaussian_sum_le (fun i ↦ mean (y i) v s) (legVariance_pos ht hs hs1).ne'
    (mul_pos (sub_pos.mpr hs1) hε) (mean_separated y v s hε.le hsep)
  have hb := collision_cubic_bound ν (∑i,μ i) (fluctuation_continuous t r w).measurable
    (fluctuation_nonneg hr.le w) (fluctuation_memLp t r s w) (c 0) hr.le (by positivity : 0≤2+A)
    (show 0≤packingConstant*(((1-(s:ℝ))*ε)⁻¹^3+(Real.sqrt ((2*(legVariance t s:ℝ))⁻¹))^3) from
      mul_nonneg packingConstant_pos.le (by positivity)) hμ
  apply hu.trans (hb.trans _)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left (add_le_add le_rfl (fluctuation_mean ht.le hr s w hscale))
  exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg packingConstant_pos.le (by positivity))) (by positivity)

end HardSphere.Bridge

end
end

end

end OAI
