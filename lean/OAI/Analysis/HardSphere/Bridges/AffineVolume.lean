import Mathlib
import OAI.Analysis.HardSphere.Bridges.IncrementMoment

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

def affine (s : ℝ) (c : Point) (x : Point) : Point := fun j ↦ s*x j+c j
lemma affine_measurable (s : ℝ) (c : Point) : Measurable (affine s c) := by unfold affine; fun_prop
lemma affine_volume {s : ℝ} (hs : 0<s) (c : Point) :
    (volume : Measure Point).map (affine s c)=ENNReal.ofReal (s⁻¹^3) • volume := by
  let F : Point →ₗ[ℝ] Point := s • LinearMap.id
  have hF : LinearMap.det F=s^3 := by simp [F,LinearMap.det_smul]
  have hFn : LinearMap.det F≠0 := by rw [hF]; positivity
  have he : affine s c=(fun x : Point ↦ x+c) ∘ F := rfl
  rw [he,←Measure.map_map (by fun_prop) F.continuous_of_finiteDimensional.measurable,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hFn,Measure.map_smul _ (by fun_prop),
    (measurePreserving_add_right (volume : Measure Point) c).map_eq,hF]
  congr 2
  rw [abs_of_pos (by positivity),inv_pow]

lemma affine_restrict_le (B : Set Point) {s : ℝ} (hs : 0<s) (c : Point) :
    ((volume : Measure Point).restrict B).map (affine s c) ≤ ENNReal.ofReal (s⁻¹^3) • volume := by
  rw [←affine_volume hs c]
  exact Measure.map_mono Measure.restrict_le_self (affine_measurable s c)

lemma affine_kernel_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [SFinite ν]
    {c : Ω → Point} (hc : Measurable c) (B : Set Point) {s : ℝ} (hs : 0<s) :
    (ν.prod ((volume : Measure Point).restrict B)).map (fun p ↦ (p.1,affine s (c p.1) p.2)) ≤
      ν.prod (ENNReal.ofReal (s⁻¹^3) • (volume : Measure Point)) := by
  have hm : Measurable (fun p : Ω×Point ↦ (p.1,affine s (c p.1) p.2)) := by
    apply measurable_fst.prodMk
    unfold affine
    exact Measurable.of_eval fun coordinate ↦
      ((measurable_pi_apply coordinate).comp measurable_snd |>.const_mul s).add
        ((measurable_pi_apply coordinate).comp (hc.comp measurable_fst))
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.map_apply hm hE,Measure.prod_apply (hE.preimage hm),Measure.prod_apply hE]
  apply lintegral_mono
  intro ω
  have hsec : MeasurableSet {x : Point | (ω,x)∈E} := hE.preimage measurable_prodMk_left
  change ((volume : Measure Point).restrict B) ((affine s (c ω))⁻¹' {x | (ω,x)∈E}) ≤ _
  rw [←Measure.map_apply (affine_measurable s (c ω)) hsec]
  exact affine_restrict_le B hs (c ω) _

end HardSphere.GaussianPacking

namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma leg_segment_increment (t : ℝ) (y v : Point) (β : Noise) (s q : Time) (j : Fin 3) :
    leg t y v β (suffixTime s q) j=leg t y v β s j+
      ((1-(s:ℝ))*(q:ℝ))*(v j-y j)+Real.sqrt (2*t)*(β j (suffixTime s q)-β j s) := by
  simp only [leg,ContinuousMap.coe_mk,mean]
  dsimp [suffixTime]
  ring

def uniformSegmentHit (t : ℝ) (y : Point) (s w : Time) (c : Time → Point) (r : ℝ) (B : Set Point) : Set (Noise×Point) :=
  {p | p.2∈B ∧ ∃q : Time,(q:ℝ) ≤ (w:ℝ) ∧ ‖leg t y p.2 p.1 (suffixTime s q)-c q‖ ≤ r}

lemma uniform_segment_necessary {t r C A : ℝ} (hr : 0<r) (hC : 0 ≤ C) (y : Point) (s w : Time)
    (c : Time → Point) (B : Set Point) (hB : ∀v∈B,‖v-y‖ ≤ C)
    (hA : ∀q : Time,(q:ℝ) ≤ (w:ℝ) → ‖c q-c 0‖ ≤ r*A)
    (hdrift : ((1-(s:ℝ))*(w:ℝ))*C ≤ r) : uniformSegmentHit t y s w c r B ⊆
      {p | leg t y p.2 p.1 s ∈ cube (c 0) (r*(2+A+incrementFluctuation t r s w p.1))} := by
  rintro p ⟨hp,q,hq,hh⟩
  have hc := hB p.2 hp
  have hs0 := sub_nonneg.mpr s.property.2
  have hb (j : Fin 3) : |leg t y p.2 p.1 s j-c 0 j| ≤ r*(2+A+incrementFluctuation t r s w p.1) := by
    have hi : |leg t y p.2 p.1 (suffixTime s q) j-c q j| ≤ r := (norm_le_pi_norm _ j).trans hh
    have ho : |c q j-c 0 j| ≤ r*A := (norm_le_pi_norm _ j).trans (hA q hq)
    have hd : |((1-(s:ℝ))*(q:ℝ))*(p.2 j-y j)| ≤ r := by
      rw [abs_mul,abs_of_nonneg (mul_nonneg hs0 q.property.1)]
      exact (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ j).trans hc) (mul_nonneg hs0 q.property.1)).trans
        ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hs0) hC).trans hdrift)
    have hn := incrementFluctuation_eval (t:=t) hr s w q hq p.1 j
    have he : leg t y p.2 p.1 s j-c 0 j=
        ((leg t y p.2 p.1 (suffixTime s q) j-c q j)+(c q j-c 0 j))-
        ((1-(s:ℝ))*(q:ℝ))*(p.2 j-y j)-Real.sqrt (2*t)*(p.1 j (suffixTime s q)-p.1 j s) := by
      rw [leg_segment_increment]; ring
    rw [he]
    calc
      _ ≤ (|leg t y p.2 p.1 (suffixTime s q) j-c q j|+|c q j-c 0 j|)+
          |((1-(s:ℝ))*(q:ℝ))*(p.2 j-y j)|+|Real.sqrt (2*t)*(p.1 j (suffixTime s q)-p.1 j s)| :=
        (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ (r+r*A)+r+r*incrementFluctuation t r s w p.1 := by gcongr
      _ = _ := by ring
  exact ⟨fun j ↦ by have h := (abs_le.mp (hb j)).1; dsimp; linarith,
    fun j ↦ by have h := (abs_le.mp (hb j)).2; dsimp; linarith⟩

lemma uniform_position_le (t : ℝ) (y : Point) (s : Time) (hs : 0<(s:ℝ)) (B : Set Point) :
    (law.prod ((volume : Measure Point).restrict B)).map (fun p ↦ (p.1,leg t y p.2 p.1 s)) ≤
      law.prod (ENNReal.ofReal ((s:ℝ)⁻¹^3) • (volume : Measure Point)) := by
  let cβ : Noise → Point := fun β j ↦ (1-(s:ℝ))*y j+Real.sqrt (2*t)*β j s
  have hc : Measurable cβ := by
    apply Continuous.measurable
    dsimp [cβ]
    fun_prop
  have he (p : Noise×Point) : affine (s:ℝ) (cβ p.1) p.2=leg t y p.2 p.1 s := by
    ext j
    simp only [affine,cβ,leg,ContinuousMap.coe_mk,mean]
    ring
  simpa only [he] using affine_kernel_le law hc B hs

lemma uniform_segment_bound (y : Point) (s w : Time) (c : Time → Point) (B : Set Point)
    {t r C A : ℝ} (ht : 0<t) (hr : 0<r) (hC : 0 ≤ C) (hA0 : 0 ≤ A)
    (hs : 0<(s:ℝ)) (hB : ∀v∈B,‖v-y‖ ≤ C)
    (hA : ∀q : Time,(q:ℝ) ≤ (w:ℝ) → ‖c q-c 0‖ ≤ r*A)
    (hdrift : ((1-(s:ℝ))*(w:ℝ))*C ≤ r) (hscale : t*(1-(s:ℝ))*(w:ℝ) ≤ r^2) :
    (law.prod ((volume : Measure Point).restrict B)) (uniformSegmentHit t y s w c r B) ≤
      ENNReal.ofReal (32*(s:ℝ)⁻¹^3*r^3*((2+A)^3+3072*normCubeMean)) := by
  let E := {p : Noise×Point | p.2∈cube (c 0) (r*((2+A)+incrementFluctuation t r s w p.1))}
  have hE : MeasurableSet E := measurable_cube_event (incrementFluctuation_continuous t r s w).measurable (c 0) r (2+A)
  have hm : Measurable (fun p : Noise×Point ↦ (p.1,leg t y p.2 p.1 s)) := by
    apply measurable_fst.prodMk
    change Measurable (fun p : Noise×Point ↦ fun j ↦ (1-(s:ℝ))*y j+(s:ℝ)*p.2 j+Real.sqrt (2*t)*p.1 j s)
    fun_prop
  have hu := measure_mono (μ:=law.prod ((volume : Measure Point).restrict B)) (uniform_segment_necessary (t:=t) hr hC y s w c B hB hA hdrift)
  have he : {p : Noise×Point | leg t y p.2 p.1 s∈cube (c 0) (r*(2+A+incrementFluctuation t r s w p.1))}=
      (fun p : Noise×Point ↦ (p.1,leg t y p.2 p.1 s))⁻¹' E := rfl
  rw [he,←Measure.map_apply hm hE] at hu
  apply (hu.trans (uniform_position_le t y s hs B E)).trans
  have hμ : ENNReal.ofReal ((s:ℝ)⁻¹^3) • (volume : Measure Point) ≤ ENNReal.ofReal ((s:ℝ)⁻¹^3) • volume := le_rfl
  have hb := collision_cubic_bound law (ENNReal.ofReal ((s:ℝ)⁻¹^3) • (volume : Measure Point))
    (incrementFluctuation_continuous t r s w).measurable (incrementFluctuation_nonneg hr.le s w)
    (incrementFluctuation_memLp t r s w) (c 0) hr.le (by positivity : 0 ≤ 2+A) (by positivity : 0 ≤ (s:ℝ)⁻¹^3) hμ
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left (add_le_add le_rfl (incrementFluctuation_mean ht.le hr s w hscale))
  positivity

end HardSphere.Bridge

end

end OAI
