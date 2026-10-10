import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.AngularMoment2
import OAI.MeasureTheory.FalconerCompletion.Shells.IntegrableCoeffNormPower

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory
open scoped ComplexConjugate
variable {V : Type*} [MeasurableSpace V]

noncomputable def sourceAngularCorrelationND (μ : Measure V) (ψ : V → ℂ)
    (U W : ℝ × V → ℂ) (r : ℝ) : ℂ := ∫ w, ψ w*U (r,w)*conj (W (r,w)) ∂μ

lemma sourceAngularCorrelationND_measurable (μ : Measure V) [SFinite μ]
    {ψ : V → ℂ} (hψ : Measurable ψ) {U W : ℝ × V → ℂ}
    (hU : Measurable U) (hW : Measurable W) :
    Measurable (sourceAngularCorrelationND μ ψ U W) :=
  (((hψ.comp measurable_snd).mul hU).mul
    (Complex.continuous_conj.measurable.comp hW)).stronglyMeasurable.integral_prod_right'.measurable

lemma sourceAngularCorrelationND_bound (μ : Measure V) [IsFiniteMeasure μ]
    (ψ : V → ℂ) (U W : ℝ × V → ℂ) {P C D : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hbψ : ∀ w, ‖ψ w‖ ≤ P) (hbU : ∀ r w, ‖U (r,w)‖ ≤ C)
    (hbW : ∀ r w, ‖W (r,w)‖ ≤ D) (r : ℝ) :
    ‖sourceAngularCorrelationND μ ψ U W r‖ ≤ P*C*D*μ.real univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards with w
  simp only [norm_mul,Complex.norm_conj]
  exact mul_le_mul (mul_le_mul (hbψ w) (hbU r w) (norm_nonneg _) hP)
    (hbW r w) (norm_nonneg _) (mul_nonneg hP hC)

lemma sourceAngularCorrelationND_weighted_integrable (μ : Measure V) [IsFiniteMeasure μ]
    {ψ : V → ℂ} (hψ : Measurable ψ) {U W : ℝ × V → ℂ}
    (hU : Measurable U) (hW : Measurable W) {P C D : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hbψ : ∀ w, ‖ψ w‖ ≤ P) (hbU : ∀ r w, ‖U (r,w)‖ ≤ C)
    (hbW : ∀ r w, ‖W (r,w)‖ ≤ D) {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ) :
    Integrable (fun r => Ψ r*‖sourceAngularCorrelationND μ ψ U W r‖^2) := by
  apply (hΨ.norm.mul_const ((P*C*D*μ.real univ)^2)).mono'
    (hΨ.aestronglyMeasurable.mul
      ((sourceAngularCorrelationND_measurable μ hψ hU hW).norm.pow_const 2).aestronglyMeasurable)
  filter_upwards with r
  dsimp only [Pi.mul_apply]
  rw [norm_mul,Real.norm_eq_abs (‖sourceAngularCorrelationND μ ψ U W r‖^2),
    abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
    (sourceAngularCorrelationND_bound μ ψ U W hP hC hbψ hbU hbW r) 2) (norm_nonneg _)

theorem sourceAngularHFND_shell_bound (d : ℕ) (μ : Measure V) [IsFiniteMeasure μ]
    (a v : ℝ) {ψ : V → ℂ} (hψ : Measurable ψ) {U W : ℝ × V → ℂ}
    (hU : Measurable U) (hW : Measurable W) {P C D : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hbψ : ∀ w, ‖ψ w‖ ≤ P) (hbU : ∀ r w, ‖U (r,w)‖ ≤ C)
    (hbW : ∀ r w, ‖W (r,w)‖ ≤ D) {Ψ : ℝ → ℝ}
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hΨpos : ∀ r, 0 ≤ Ψ r)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) :
    (∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ‖sourceAngularCorrelationND μ ψ U W r‖^2) ≤
      ((2:ℝ)^((d:ℝ)*(v-a)))⁻¹*(2:ℝ)^v*sourceAngularHFND d μ a v Ψ ψ U W := by
  have hΩ : 0 < (2:ℝ)^v := by positivity
  have hK : (2:ℝ)^((d:ℝ)*(v-a)) ≠ 0 := (by positivity : (0:ℝ)<(2:ℝ)^((d:ℝ)*(v-a))).ne'
  have hi := sourceAngularCorrelationND_weighted_integrable μ hψ hU hW hP hC hbψ hbU hbW hΨ
  have his : IntegrableOn (fun r => ‖sourceAngularCorrelationND μ ψ U W r‖^2)
      (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v)) := by
    apply Integrable.of_bound
      (((sourceAngularCorrelationND_measurable μ hψ hU hW).norm.pow_const 2).aestronglyMeasurable)
      ((P*C*D*μ.real univ)^2)
    filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (sourceAngularCorrelationND_bound μ ψ U W hP hC hbψ hbU hbW r) 2
  have hle : (∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ‖sourceAngularCorrelationND μ ψ U W r‖^2) ≤
      ∫ r, Ψ (r/(2:ℝ)^v)*‖sourceAngularCorrelationND μ ψ U W r‖^2 := by
    apply le_trans (setIntegral_mono_on his hi.integrableOn measurableSet_Icc ?_)
      (setIntegral_le_integral hi (Filter.Eventually.of_forall (fun r => mul_nonneg (hΨpos _) (sq_nonneg _))))
    intro r hr
    have hin : r/(2:ℝ)^v ∈ Icc (1/2:ℝ) 2 := by
      constructor
      · exact (le_div_iff₀ hΩ).mpr (by linarith [hr.1])
      · exact (div_le_iff₀ hΩ).mpr hr.2
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hone _ hin)
      (sq_nonneg ‖sourceAngularCorrelationND μ ψ U W r‖)
  convert hle using 1
  simp only [sourceAngularHFND,sourceAngularCorrelationND]
  field_simp

lemma weighted_shell_normalizationND (n : ℕ) (a v : ℝ) :
    (2:ℝ)^(-a)*(2:ℝ)^((n:ℝ)*(v-a))*
      (((2:ℝ)^(((n+1:ℕ):ℝ)*(v-a)))⁻¹*(2:ℝ)^v) = 1 := by
  rw [← Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  simp only [Nat.cast_add,Nat.cast_one]
  repeat rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  convert (Real.rpow_zero (2:ℝ)) using 1
  ring_nf
  norm_num [Real.rpow_zero]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory
open scoped ComplexConjugate
variable {α V : Type*} [MeasurableSpace α] [MeasurableSpace V]

lemma sourceAngularCorrelationND_parameter_measurable (μ : Measure V) [SFinite μ]
    {ψ : V → ℂ} (hψ : Measurable ψ) {U W : α × (ℝ × V) → ℂ}
    (hU : Measurable U) (hW : Measurable W) :
    Measurable (fun p : α × ℝ => sourceAngularCorrelationND μ ψ
      (fun z => U (p.1,z)) (fun z => W (p.1,z)) p.2) := by
  have hc : Measurable (fun p : (α × ℝ) × V => (p.1.1,(p.1.2,p.2))) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  exact (((hψ.comp measurable_snd).mul (hU.comp hc)).mul
    (Complex.continuous_conj.measurable.comp (hW.comp hc))).stronglyMeasurable.integral_prod_right'.measurable

theorem continuous_HF_shell_boundND (d : ℕ) (ν : Measure α) [SFinite ν]
    (μ : Measure V) [IsFiniteMeasure μ] (a v : ℝ)
    (c : α → ℂ) (hc : Measurable c) (hic : Integrable c ν)
    {ψ : V → ℂ} (hψ : Measurable ψ) {U W : α × (ℝ × V) → ℂ}
    (hU : Measurable U) (hW : Measurable W) {P C D B : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hbψ : ∀ w, ‖ψ w‖ ≤ P) (hbU : ∀ ξ r w, ‖U (ξ,(r,w))‖ ≤ C)
    (hbW : ∀ ξ r w, ‖W (ξ,(r,w))‖ ≤ D) {Ψ : ℝ → ℝ}
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hΨpos : ∀ r, 0 ≤ Ψ r)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    (hB : ∀ ξ, sourceAngularHFND d μ a v Ψ ψ
      (fun z => U (ξ,z)) (fun z => W (ξ,z)) ≤ B) :
    (∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v),
      ‖∫ ξ, c ξ*sourceAngularCorrelationND μ ψ
        (fun z => U (ξ,z)) (fun z => W (ξ,z)) r ∂ν‖^2) ≤
      (∫ ξ, ‖c ξ‖ ∂ν)^2 * (((2:ℝ)^((d:ℝ)*(v-a)))⁻¹*(2:ℝ)^v*B) := by
  apply ShellND.continuous_coefficient_shell_square ν _ c hc hic _
    (sourceAngularCorrelationND_parameter_measurable μ hψ hU hW)
    (C := P*C*D*μ.real univ)
  · intro p
    exact sourceAngularCorrelationND_bound μ ψ _ _ hP hC hbψ (hbU p.1) (hbW p.1) p.2
  · intro ξ
    exact (sourceAngularHFND_shell_bound d μ a v hψ
      (hU.comp (measurable_const.prodMk measurable_id))
      (hW.comp (measurable_const.prodMk measurable_id)) hP hC hbψ (hbU ξ) (hbW ξ)
        hΨ hΨpos hone).trans (mul_le_mul_of_nonneg_left (hB ξ) (by positivity))

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory

lemma shell_square_multiplierND (μ : Measure ℝ) {F m : ℝ → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable (fun r => m r*F r) μ)
    (hi : Integrable (fun r => ‖F r‖^2) μ) (hb : ∀ᵐ r ∂μ, ‖m r‖ ≤ C) :
    Integrable (fun r => ‖m r*F r‖^2) μ ∧
      (∫ r, ‖m r*F r‖^2 ∂μ) ≤ C^2*(∫ r, ‖F r‖^2 ∂μ) := by
  have hp : ∀ᵐ r ∂μ, ‖m r*F r‖^2 ≤ C^2*‖F r‖^2 := by
    filter_upwards [hb] with r hr
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hr 2) (sq_nonneg _)
  have hfull : Integrable (fun r => ‖m r*F r‖^2) μ := by
    apply (hi.const_mul (C^2)).mono' (hm.norm.pow 2)
    filter_upwards [hp] with r hr
    rwa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  refine ⟨hfull,?_⟩
  calc
    _ ≤ ∫ r, C^2*‖F r‖^2 ∂μ := integral_mono_ae hfull (hi.const_mul (C^2)) hp
    _ = _ := integral_const_mul _ _

lemma shell_add_squareND (μ : Measure ℝ) {F G : ℝ → ℂ}
    (hmF : AEStronglyMeasurable F μ) (hmG : AEStronglyMeasurable G μ)
    (hiF : Integrable (fun r => ‖F r‖^2) μ) (hiG : Integrable (fun r => ‖G r‖^2) μ) :
    (∫ r, ‖F r+G r‖^2 ∂μ) ≤ 2*(∫ r, ‖F r‖^2 ∂μ)+2*(∫ r, ‖G r‖^2 ∂μ) := by
  have hp (r : ℝ) : ‖F r+G r‖^2 ≤ 2*‖F r‖^2+2*‖G r‖^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (F r) (G r)) 2
    nlinarith [sq_nonneg (‖F r‖-‖G r‖)]
  have hi : Integrable (fun r => ‖F r+G r‖^2) μ := by
    apply ((hiF.const_mul 2).add (hiG.const_mul 2)).mono' ((hmF.add hmG).norm.pow 2)
    filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hp r
  calc
    _ ≤ ∫ r, (2*‖F r‖^2+2*‖G r‖^2) ∂μ :=
      integral_mono hi ((hiF.const_mul 2).add (hiG.const_mul 2)) hp
    _ = _ := by rw [integral_add (hiF.const_mul 2) (hiG.const_mul 2),integral_const_mul,integral_const_mul]

lemma shell_lengthND (v : ℝ) :
    (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))).real univ = 3*(2:ℝ)^v/2 := by
  rw [Measure.real,Measure.restrict_apply_univ,← Measure.real,
    Real.volume_real_Icc_of_le (by
      have hp : (0:ℝ)<2^v := by positivity
      linarith)]
  ring

lemma shell_error_squareND {v E : ℝ} {F : ℝ → ℂ}
    (hb : ∀ r ∈ Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ‖F r‖ ≤ E) :
    (∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ‖F r‖^2) ≤ (3*(2:ℝ)^v/2)*E^2 := by
  calc
    _ ≤ ∫ _ in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), E^2 := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun r => sq_nonneg _)) (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact pow_le_pow_left₀ (norm_nonneg _) (hb r hr) 2
    _ = _ := by rw [integral_const,smul_eq_mul,shell_lengthND]

lemma shell_leading_squareND (n : ℕ) (a v : ℝ) :
    ‖(((2:ℝ)^((n:ℝ)*(v-a)/2):ℝ):ℂ)‖^2 = (2:ℝ)^((n:ℝ)*(v-a)) := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity),
    ← Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  congr 1
  norm_num

theorem normalized_list_shellND {ι : Type*} (n : ℕ) (a v : ℝ) (L : List ι)
    (F : ι → ℝ → ℂ) (w : ι → ℝ) {B : ℝ}
    (hw : ∀ i ∈ L, 0 ≤ w i)
    (hi : ∀ i ∈ L, Integrable (fun r => ‖F i r‖^2)
      (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))))
    (hm : ∀ i ∈ L, AEStronglyMeasurable (F i)
      (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))))
    (hB : ∀ i ∈ L, (∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ‖F i r‖^2) ≤
      (w i)^2*(((2:ℝ)^(((n+1:ℕ):ℝ)*(v-a)))⁻¹*(2:ℝ)^v*B)) :
    (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v),
      ‖(((2:ℝ)^((n:ℝ)*(v-a)/2):ℝ):ℂ)*(L.map (fun i => F i r)).sum‖^2) ≤
      (L.map w).sum^2*B := by
  simp_rw [norm_mul,mul_pow,shell_leading_squareND]
  rw [integral_const_mul,← mul_assoc]
  have hh := ShellND.list_weighted_shell_square L
    (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))) F w hw hi hm hB
  apply le_trans (mul_le_mul_of_nonneg_left hh (by positivity))
  have hnorm := weighted_shell_normalizationND n a v
  apply le_of_eq
  calc
    _ = ((2:ℝ)^(-a)*(2:ℝ)^((n:ℝ)*(v-a)) *
      (((2:ℝ)^(((n+1:ℕ):ℝ)*(v-a)))⁻¹*(2:ℝ)^v)) * ((L.map w).sum^2*B) := by ring
    _ = _ := by rw [hnorm,one_mul]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory

lemma integrable_add_squareND (μ : Measure ℝ) {F G : ℝ → ℂ}
    (hmF : AEStronglyMeasurable F μ) (hmG : AEStronglyMeasurable G μ)
    (hiF : Integrable (fun r => ‖F r‖^2) μ) (hiG : Integrable (fun r => ‖G r‖^2) μ) :
    Integrable (fun r => ‖F r+G r‖^2) μ := by
  apply ((hiF.const_mul 2).add (hiG.const_mul 2)).mono' ((hmF.add hmG).norm.pow 2)
  filter_upwards with r
  simp only [Pi.add_apply,Pi.pow_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (F r) (G r)) 2
  nlinarith [sq_nonneg (‖F r‖-‖G r‖)]

lemma list_shell_integrabilityND {ι : Type*} (μ : Measure ℝ) (L : List ι)
    (F : ι → ℝ → ℂ) (hm : ∀ i ∈ L, AEStronglyMeasurable (F i) μ)
    (hi : ∀ i ∈ L, Integrable (fun r => ‖F i r‖^2) μ) :
    AEStronglyMeasurable (fun r => (L.map (fun i => F i r)).sum) μ ∧
      Integrable (fun r => ‖(L.map (fun i => F i r)).sum‖^2) μ := by
  induction L with
  | nil => simp only [List.map_nil,List.sum_nil,norm_zero,zero_pow (by omega : 2 ≠ 0)];
           exact ⟨aestronglyMeasurable_const,integrable_zero _ _ _⟩
  | cons i L ih =>
    have hm' := ih (fun j hj => hm j (List.mem_cons_of_mem i hj))
      (fun j hj => hi j (List.mem_cons_of_mem i hj))
    simp only [List.map_cons,List.sum_cons]
    exact ⟨(hm i (List.mem_cons_self)).add hm'.1,
      integrable_add_squareND μ (hm i (List.mem_cons_self)) hm'.1
        (hi i (List.mem_cons_self)) hm'.2⟩

theorem normalized_list_shell_remainderND {ι : Type*} (n : ℕ) (a v : ℝ) (L : List ι)
    (F : ι → ℝ → ℂ) (w : ι → ℝ) (H : ℝ → ℂ) {B E : ℝ}
    (hw : ∀ i ∈ L, 0 ≤ w i)
    (hi : ∀ i ∈ L, Integrable (fun r => ‖F i r‖^2)
      (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))))
    (hm : ∀ i ∈ L, AEStronglyMeasurable (F i)
      (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))))
    (hB : ∀ i ∈ L, (∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ‖F i r‖^2) ≤
      (w i)^2*(((2:ℝ)^(((n+1:ℕ):ℝ)*(v-a)))⁻¹*(2:ℝ)^v*B))
    (hH : AEStronglyMeasurable H (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))))
    (hE : ∀ r ∈ Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v),
      ‖H r-(((2:ℝ)^((n:ℝ)*(v-a)/2):ℝ):ℂ)*(L.map (fun i => F i r)).sum‖ ≤ E) :
    Integrable (fun r => ‖H r‖^2) (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))) ∧
    (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ‖H r‖^2) ≤
      2*(L.map w).sum^2*B + 3*(2:ℝ)^(v-a)*E^2 := by
  let μ := volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))
  let c : ℂ := (((2:ℝ)^((n:ℝ)*(v-a)/2):ℝ):ℂ)
  let U : ℝ → ℂ := fun r => c*(L.map (fun i => F i r)).sum
  obtain ⟨hUm,hUi⟩ := list_shell_integrabilityND μ L F hm hi
  have hUm' : AEStronglyMeasurable U μ := hUm.const_mul c
  have hUi' : Integrable (fun r => ‖U r‖^2) μ := by
    simpa only [U,norm_mul,mul_pow] using hUi.const_mul (‖c‖^2)
  have hEi : Integrable (fun r => ‖H r-U r‖^2) μ := by
    apply (integrable_const (E^2)).mono' ((hH.sub hUm').norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hE r hr) 2
  have hHi := integrable_add_squareND μ hUm' (hH.sub hUm') hUi' hEi
  have hpoint (r : ℝ) : U r+(H r-U r)=H r := by ring
  simp only [Pi.sub_apply,hpoint] at hHi
  refine ⟨hHi,?_⟩
  have hh := shell_add_squareND μ hUm' (hH.sub hUm') hUi' hEi
  simp only [Pi.sub_apply,hpoint] at hh
  have he := shell_error_squareND (F := fun r => H r-U r) hE
  have hn := normalized_list_shellND n a v L F w hw hi hm hB
  change (2:ℝ)^(-a)*(∫ r, ‖U r‖^2 ∂μ) ≤ _ at hn
  have hp : 0 ≤ (2:ℝ)^(-a) := by positivity
  have hpow : (2:ℝ)^(-a)*(2:ℝ)^v = (2:ℝ)^(v-a) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  calc
    _ ≤ (2:ℝ)^(-a)*(2*(∫ r, ‖U r‖^2 ∂μ)+2*(∫ r, ‖H r-U r‖^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hh hp
    _ = 2*((2:ℝ)^(-a)*(∫ r, ‖U r‖^2 ∂μ))+
      2*(2:ℝ)^(-a)*(∫ r, ‖H r-U r‖^2 ∂μ) := by ring
    _ ≤ 2*((L.map w).sum^2*B)+2*(2:ℝ)^(-a)*((3*(2:ℝ)^v/2)*E^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hn (by norm_num))
        (mul_le_mul_of_nonneg_left he (by positivity))
    _ = _ := by nlinarith [hpow]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
