import OAI.Geometry.TranslativeCovering.CylinderProbability

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace TargetSampling
open Set MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
variable {Ω : Type u_1} [MeasurableSpace Ω]

lemma pair_preserving (P : Measure Ω) [IsProbabilityMeasure P] {M : ℕ}
    {i j : Fin M} (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin M → Ω => (x i,x j)) (Measure.pi (fun _ => P)) (P.prod P) := by
  have hind : iIndepFun (fun i (x : Fin M → Ω) => x i) (Measure.pi (fun _ => P)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),?_⟩
  have h := IndepFun.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable (hind.indepFun hij)
  rw [(measurePreserving_eval (fun _ : Fin M => P) i).map_eq,
    (measurePreserving_eval (fun _ : Fin M => P) j).map_eq] at h
  exact h

noncomputable def pairs (M : ℕ) : Finset (Fin M × Fin M) :=
  univ.filter (fun p => p.1 ≠ p.2)

noncomputable def score {M : ℕ} (A : Set (Ω × Ω)) (x : Fin M → Ω) : ℝ :=
  ∑ p ∈ pairs M,A.indicator (fun _ => 1) (x p.1,x p.2)

omit [MeasurableSpace Ω] in
lemma score_nonneg {M : ℕ} (A : Set (Ω × Ω)) (x : Fin M → Ω) : 0 ≤ score A x := by
  apply sum_nonneg
  intro p _
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma score_integrable (P : Measure Ω) [IsProbabilityMeasure P] {M : ℕ}
    {A : Set (Ω × Ω)} (hA : MeasurableSet A) :
    Integrable (score (M := M) A) (Measure.pi (fun _ => P)) := by
  apply integrable_finsetSum
  intro p _
  have he : (fun x : Fin M → Ω => A.indicator (fun _ => (1:ℝ)) (x p.1,x p.2)) =
      ((fun x : Fin M → Ω => (x p.1,x p.2)) ⁻¹' A).indicator (fun _ => 1) := by
    ext x; exact (indicator_comp_right _).symm
  rw [he]
  exact (integrable_const _).indicator (hA.preimage ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)))

lemma score_integral (P : Measure Ω) [IsProbabilityMeasure P] {M : ℕ}
    {A : Set (Ω × Ω)} (hA : MeasurableSet A) :
    (∫ x,score (M := M) A x ∂Measure.pi (fun _ => P)) =
      ((pairs M).card:ℝ)*(P.prod P).real A := by
  change (∫ x, ∑ p ∈ pairs M, A.indicator (fun _ => (1:ℝ)) (x p.1,x p.2) ∂Measure.pi (fun _ => P)) = _
  rw [integral_finsetSum]
  · have he (p : Fin M × Fin M) (hp : p ∈ pairs M) :
        (∫ x : Fin M → Ω,A.indicator (fun _ => (1:ℝ)) (x p.1,x p.2) ∂Measure.pi (fun _ => P)) =
          (P.prod P).real A := by
      have hm := pair_preserving P ((mem_filter.mp hp).2)
      have hc := integral_map (μ := Measure.pi (fun _ : Fin M => P)) hm.measurable.aemeasurable
        ((stronglyMeasurable_const (b := (1:ℝ))).indicator hA).aestronglyMeasurable
      rw [hm.map_eq] at hc
      rw [← hc,integral_indicator hA,integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one]
    rw [Finset.sum_congr rfl he]
    simp
  · intro p hp
    have hm := pair_preserving P ((mem_filter.mp hp).2)
    exact hm.integrable_comp ((stronglyMeasurable_const.indicator hA).aestronglyMeasurable) |>.mpr
      ((integrable_const _).indicator hA)

omit [MeasurableSpace Ω] in
lemma score_ge_one {M : ℕ} {A : Set (Ω × Ω)} {x : Fin M → Ω} {i j : Fin M}
    (hij : i ≠ j) (hA : (x i,x j) ∈ A) : 1 ≤ score A x := by
  classical
  have hp : (i,j) ∈ pairs M := by simp [pairs,hij]
  have h := single_le_sum (f := fun p : Fin M × Fin M => A.indicator (fun _ => (1:ℝ)) (x p.1,x p.2)) (fun p (_hp : p ∈ pairs M) =>
    Set.indicator_nonneg (fun _ _ => (zero_le_one : (0:ℝ) ≤ 1)) (x p.1,x p.2)) hp
  simpa [score,indicator_of_mem hA] using h

lemma ae_distinct (P : Measure Ω) [IsProbabilityMeasure P] [NullSingletonClass P]
    {M : ℕ} (hd : MeasurableSet (diagonal Ω)) :
    ∀ᵐ x : Fin M → Ω ∂Measure.pi (fun _ => P), Function.Injective x := by
  have hzero : (P.prod P) (diagonal Ω) = 0 := by
    rw [Measure.prod_apply hd]
    have he (x : Ω) : Prod.mk x ⁻¹' diagonal Ω = {x} := by ext y; simp [diagonal,eq_comm]
    simp_rw [he,measure_singleton]
    simp
  have hp (i j : Fin M) : ∀ᵐ x : Fin M → Ω ∂Measure.pi (fun _ => P), i ≠ j → x i ≠ x j := by
    by_cases hij : i = j
    · simp [hij]
    · have hm := (pair_preserving P hij).measure_preimage hd.nullMeasurableSet
      rw [hzero] at hm
      have hae : ∀ᵐ x : Fin M → Ω ∂Measure.pi (fun _ => P), (x i,x j) ∉ diagonal Ω := by
        apply ae_iff.mpr
        simpa only [not_not,Set.preimage,Set.mem_ofPred_eq] using hm
      filter_upwards [hae] with x hx
      simpa [diagonal] using (fun _ : i ≠ j => hx)
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hp i)] with x hx
  exact fun i j he => by_contra fun hij => hx i j hij he

lemma ae_in_set (P : Measure Ω) [IsProbabilityMeasure P] {M : ℕ} {G : Set Ω}
    (hG : MeasurableSet G) (hlarge : P Gᶜ = 0) :
    ∀ᵐ x : Fin M → Ω ∂Measure.pi (fun _ => P), ∀ i,x i ∈ G := by
  apply ae_all_iff.mpr
  intro i
  apply ae_iff.mpr
  have h := (measurePreserving_eval (fun _ : Fin M => P) i).measure_preimage hG.compl.nullMeasurableSet
  change (Measure.pi fun _ : Fin M => P) ((Function.eval i) ⁻¹' Gᶜ) = 0
  simpa only [hlarge] using h

theorem select (P : Measure Ω) [IsProbabilityMeasure P] [NullSingletonClass P]
    {M : ℕ} (hM : 2 ≤ M) (hd : MeasurableSet (diagonal Ω))
    {G : Set Ω} (hG : MeasurableSet G) (hGfull : P Gᶜ = 0)
    {A B : Set (Ω × Ω)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {p f : ℝ} (hf : 0 < f)
    (hsmall : ((pairs M).card:ℝ)*p < 1/2)
    (hPA : (P.prod P).real A ≤ p) (hPB : (P.prod P).real B ≤ f) :
    ∃ x : Fin M → Ω, (∀ i,x i ∈ G) ∧ Function.Injective x ∧
      (∀ i j,i ≠ j → (x i,x j) ∉ A) ∧
      score B x ≤ 10*((pairs M).card:ℝ)*f := by
  have hK : 0 < ((pairs M).card:ℝ) := by
    have hne : (pairs M).Nonempty := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by simp [pairs,Fin.ext_iff]⟩
    exact_mod_cast card_pos.mpr hne
  let q : ℝ := 10*((pairs M).card:ℝ)*f
  have hq : 0 < q := by dsimp [q]; positivity
  let W := fun x : Fin M → Ω => score A x+score B x/q
  have hWi : Integrable W (Measure.pi (fun _ => P)) :=
    (score_integrable P hA).add ((score_integrable P hB).div_const q)
  have hW : (∫ x,W x ∂Measure.pi (fun _ => P)) < 1 := by
    rw [integral_add (score_integrable P hA) ((score_integrable P hB).div_const q),
      integral_div,score_integral P hA,score_integral P hB]
    have h1 := mul_le_mul_of_nonneg_left hPA hK.le
    have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPB hK.le) hq.le
    have he : ((pairs M).card:ℝ)*f/q = 1/10 := by dsimp [q]; field_simp
    rw [he] at h2
    linarith
  let N := {x : Fin M → Ω | ¬((∀ i,x i ∈ G) ∧ Function.Injective x)}
  have hN : Measure.pi (fun _ : Fin M => P) N = 0 := by
    apply ae_iff.mp
    filter_upwards [ae_in_set P hG hGfull,ae_distinct P hd] with x hx hy
    exact ⟨hx,hy⟩
  obtain ⟨x,hx,hWx⟩ := exists_notMem_null_le_integral hWi hN
  have hWx' : W x < 1 := hWx.trans_lt hW
  have hx' : (∀ i,x i ∈ G) ∧ Function.Injective x := not_not.mp hx
  refine ⟨x,hx'.1,hx'.2,?_,?_⟩
  · intro i j hij ha
    have h1 := score_ge_one hij ha
    have h2 := div_nonneg (score_nonneg B x) hq.le
    dsimp [W] at hWx'
    linarith
  · have h1 := score_nonneg A x
    have h2 : score B x/q < 1 := by dsimp [W] at hWx'; linarith
    have h3 := (div_lt_one hq).mp h2
    exact h3.le

end TargetSampling

end OAI
