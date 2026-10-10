import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience.AnchorSampling

variable {I H : Type*} [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]

noncomputable def atomError (ν : Measure H) (F : H → H) (u v : H) : ℝ :=
  (if v=F u then 1 else 0)-ν.real {F u}

omit [Countable H] [MeasurableSingletonClass H] in
lemma atomMass_mem (ν : Measure H) [IsProbabilityMeasure ν] (x : H) :
    ν.real {x} ∈ Set.Icc (0:ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩

omit [Countable H] [MeasurableSingletonClass H] in
lemma atomError_bound (ν : Measure H) [IsProbabilityMeasure ν] (F : H → H) (u v : H) :
    ‖atomError ν F u v‖≤1 := by
  have h := atomMass_mem ν (F u)
  rw [Real.norm_eq_abs,abs_le]
  unfold atomError
  split_ifs <;> constructor <;> linarith [h.1,h.2]

lemma atomError_integrable (ν : Measure H) [IsProbabilityMeasure ν] (F : H → H) (u : H) :
    Integrable (atomError ν F u) ν :=
  (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall (atomError_bound ν F u))

lemma integral_atomError (ν : Measure H) [IsProbabilityMeasure ν] (F : H → H) (u : H) :
    (∫ v, atomError ν F u v ∂ν)=0 := by
  have hi : Integrable (fun v : H => if v=F u then (1:ℝ) else 0) ν :=
    (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by split_ifs <;> norm_num)
  have he : (∫ v : H, (if v=F u then (1:ℝ) else 0) ∂ν)=ν.real {F u} := by
    simpa only [Set.indicator_apply,Set.mem_singleton_iff,Pi.one_apply] using
      (integral_indicator_one (μ:=ν) (measurableSet_singleton (F u)))
  simp only [atomError,integral_sub hi (integrable_const _),he,integral_const,probReal_univ,smul_eq_mul,one_mul,sub_self]

lemma pair_sampling_test (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : H → H) (G : H → ℝ) (C : ℝ) (hG : ∀ u, ‖G u‖≤C) :
    (∫ p : H×H, G p.1*atomError ν F p.1 p.2 ∂μ.prod ν)=0 := by
  have hb (p : H×H) : ‖G p.1*atomError ν F p.1 p.2‖≤C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (atomError_bound ν F p.1 p.2) (norm_nonneg _)).trans
      (by simpa using hG p.1)
  have hi := (integrable_const C (μ:=μ.prod ν)).mono' (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  rw [integral_prod _ hi]
  simp only [integral_const_mul,integral_atomError,mul_zero,integral_zero]

lemma infinitePi_sampling_test (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (p q : I) (hpq : p≠q) (F : H → H) (G : H → ℝ) (C : ℝ) (hG : ∀ u, ‖G u‖≤C) :
    (∫ U, G (U p)*atomError (μ q) F (U p) (U q) ∂Measure.infinitePi μ)=0 := by
  have he := Measure.infinitePi_map_eval_prod (P:=μ) hpq
  have hm : Measurable (fun U : I → H => (U p,U q)) := (measurable_pi_apply p).prodMk (measurable_pi_apply q)
  rw [←integral_map hm.aemeasurable (measurable_of_countable
    (fun t : H×H => G t.1*atomError (μ q) F t.1 t.2)).aestronglyMeasurable,he]
  exact pair_sampling_test _ _ F G C hG

omit [Countable H] [MeasurableSingletonClass H] in
lemma infinitePi_pair_fresh (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (p b c : I) (hpc : p≠c) (hbc : b≠c) :
    (Measure.infinitePi μ).map (fun U : I → H => ((U p,U b),U c)) =
      ((Measure.infinitePi μ).map (fun U => (U p,U b))).prod (μ c) := by
  have hind := (iIndepFun_infinitePi (P:=μ) (X:= fun _ x => x) (fun _ => measurable_id)).indepFun_prodMk
    (fun i => measurable_pi_apply i) p b c hpc hbc
  rw [IndepFun.map_prod_eq_prod_map_map
    ((measurable_pi_apply p).prodMk (measurable_pi_apply b)).aemeasurable
    (measurable_pi_apply c).aemeasurable hind,Measure.infinitePi_map_eval]

lemma infinitePi_atomError_cross_fresh (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure H) [IsProbabilityMeasure ν] (p b c : I) (hc : μ c=ν)
    (hpc : p≠c) (hbc : b≠c) (F : H → H) :
    (∫ U, atomError ν F (U p) (U b)*atomError ν F (U p) (U c) ∂Measure.infinitePi μ)=0 := by
  let Ψ : (H×H)×H → ℝ := fun w => atomError ν F w.1.1 w.1.2*atomError ν F w.1.1 w.2
  have hΨm : Measurable Ψ := measurable_of_countable _
  have hm : Measurable (fun U : I → H => ((U p,U b),U c)) := by fun_prop
  have hb (w) : ‖Ψ w‖≤1 := by
    change ‖atomError ν F w.1.1 w.1.2*atomError ν F w.1.1 w.2‖≤1
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (atomError_bound _ _ _ _) (norm_nonneg _)).trans
      (by simpa using atomError_bound ν F w.1.1 w.1.2)
  have hΨi : Integrable Ψ (((Measure.infinitePi μ).map (fun U => (U p,U b))).prod ν) :=
    (integrable_const (1:ℝ)).mono' hΨm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  change (∫ U, Ψ ((U p,U b),U c) ∂Measure.infinitePi μ)=0
  rw [←integral_map hm.aemeasurable hΨm.aestronglyMeasurable,
    infinitePi_pair_fresh μ p b c hpc hbc,hc,integral_prod _ hΨi]
  simp only [Ψ,integral_const_mul,integral_atomError,mul_zero,integral_zero]

lemma infinitePi_atomError_cross (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure H) [IsProbabilityMeasure ν] (p b c : I) (hb : μ b=ν) (hc : μ c=ν)
    (hbc : b≠c) (F : H → H) :
    (∫ U, atomError ν F (U p) (U b)*atomError ν F (U p) (U c) ∂Measure.infinitePi μ)=0 := by
  by_cases hpc : p=c
  · have hpb : p≠b := by simpa [hpc] using hbc.symm
    simpa only [mul_comm] using infinitePi_atomError_cross_fresh μ ν p c b hb hpb hbc.symm F
  · exact infinitePi_atomError_cross_fresh μ ν p b c hc hpc hbc F

lemma atomError_eval_measurable (ν : Measure H) (F : H → H) (p b : I) :
    Measurable (fun U : I→H => atomError ν F (U p) (U b)) := by
  have hm : Measurable (fun U : I→H => (U p,U b)) :=
    (measurable_pi_apply p).prodMk (measurable_pi_apply b)
  exact (measurable_of_countable (fun t : H×H => atomError ν F t.1 t.2)).comp hm

lemma atomError_eval_product_integrable (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure H) [IsProbabilityMeasure ν] (F : H→H) (p b c : I) :
    Integrable (fun U => atomError ν F (U p) (U b)*atomError ν F (U p) (U c)) (Measure.infinitePi μ) := by
  apply (integrable_const (1:ℝ)).mono'
    ((atomError_eval_measurable ν F p b).mul (atomError_eval_measurable ν F p c)).aestronglyMeasurable
  filter_upwards [] with U
  change ‖atomError ν F (U p) (U b)*atomError ν F (U p) (U c)‖≤1
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (atomError_bound _ _ _ _) (norm_nonneg _)).trans
    (by simpa using atomError_bound ν F (U p) (U b))

theorem infinitePi_sample_sum_sq (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure H) [IsProbabilityMeasure ν] (p : I) (S : Finset I)
    (hlaw : ∀ b∈S, μ b=ν) (F : H→H) :
    (∫ U, (∑ b∈S, atomError ν F (U p) (U b))^2 ∂Measure.infinitePi μ)≤S.card := by
  classical
  have hprod := atomError_eval_product_integrable μ ν F p
  have he (U : I→H) : (∑ b∈S, atomError ν F (U p) (U b))^2 =
      ∑ b∈S, ∑ c∈S, atomError ν F (U p) (U b)*atomError ν F (U p) (U c) := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => hprod b c))]
  simp_rw [integral_finsetSum _ (fun c _ => hprod _ c)]
  calc
    (∑ b∈S, ∑ c∈S, ∫ U, atomError ν F (U p) (U b)*atomError ν F (U p) (U c) ∂Measure.infinitePi μ)
      = ∑ b∈S, ∫ U, atomError ν F (U p) (U b)*atomError ν F (U p) (U b) ∂Measure.infinitePi μ := by
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_eq_single b
        · intro c hc hcb
          exact infinitePi_atomError_cross μ ν p b c (hlaw b hb) (hlaw c hc) hcb.symm F
        · intro h
          exact False.elim (h hb)
    _ ≤ ∑ _b∈S, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      have hle : (∫ U, atomError ν F (U p) (U b)*atomError ν F (U p) (U b) ∂Measure.infinitePi μ)≤
          ∫ _U : I→H, (1:ℝ) ∂Measure.infinitePi μ := by
        apply integral_mono (hprod b b) (integrable_const _)
        intro U
        have hh := atomError_bound ν F (U p) (U b)
        rw [Real.norm_eq_abs,abs_le] at hh
        nlinarith [sq_nonneg (atomError ν F (U p) (U b))]
      simpa using hle
    _ = S.card := by simp

theorem infinitePi_sample_average_sq (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure H) [IsProbabilityMeasure ν] (p : I) (S : Finset I)
    (hlaw : ∀ b∈S, μ b=ν) (F : H→H) :
    (∫ U, ((S.card:ℝ)⁻¹*∑ b∈S, atomError ν F (U p) (U b))^2 ∂Measure.infinitePi μ)≤(S.card:ℝ)⁻¹ := by
  simp_rw [mul_pow,integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left (infinitePi_sample_sum_sq μ ν p S hlaw F)
    (sq_nonneg (S.card:ℝ)⁻¹)
  apply hh.trans_eq
  by_cases hs : S.card=0
  · simp [hs]
  · have hn : (S.card:ℝ)≠0 := Nat.cast_ne_zero.mpr hs
    field_simp

end DirectionalTransience.AnchorSampling

end

end OAI
