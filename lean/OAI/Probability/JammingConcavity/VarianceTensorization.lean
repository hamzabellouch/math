import Mathlib
import OAI.Probability.JammingConcavity.DeletionMeasurePreservingSelectRows

namespace OAI

/-! Variance Tensorization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma memLp_two_swap {f : Ω × Ξ → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun p : Ξ × Ω => f (p.2,p.1)) 2 (ν.prod μ) :=
  hf.comp_measurePreserving (Measure.measurePreserving_swap (μ := ν) (ν := μ))

lemma integral_sq_ge_sq_integral {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  change 0 ≤ (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ)^2 at h
  linarith

lemma memLp_two_integral_snd {f : Ω × Ξ → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x => ∫ y, f (x,y) ∂ν) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable.integral_prod_right')).mpr
  have hfi := (hf.integrable one_le_two).integral_prod_left
  apply hf.integrable_sq.integral_prod_left.mono'
    (hf.aestronglyMeasurable.integral_prod_right'.pow 2)
  filter_upwards [hf.integrable_sq.prod_right_ae, (hf.integrable one_le_two).prod_right_ae]
    with x hx hx'
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply integral_sq_ge_sq_integral
  exact (memLp_two_iff_integrable_sq hx'.1).mpr hx

lemma memLp_two_fiber_ae {f : Ω × Ξ → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => f (x,y)) 2 ν := by
  filter_upwards [hf.integrable_sq.prod_right_ae, (hf.integrable one_le_two).prod_right_ae]
    with x hx hx'
  exact (memLp_two_iff_integrable_sq hx'.1).mpr hx

lemma integrable_fiber_variance {f : Ω × Ξ → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    Integrable (fun x => Var[fun y => f (x,y); ν]) μ := by
  have h := hf.integrable_sq.integral_prod_left.sub
    (memLp_two_integral_snd hf).integrable_sq
  apply h.congr
  filter_upwards [memLp_two_fiber_ae hf] with x hx
  exact (variance_eq_sub hx).symm

lemma variance_prod_eq {f : Ω × Ξ → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    Var[f; μ.prod ν] = (∫ x, Var[fun y => f (x,y); ν] ∂μ) +
      Var[fun x => ∫ y, f (x,y) ∂ν; μ] := by
  have he : (∫ x, Var[fun y => f (x,y); ν] ∂μ) =
      (∫ x, (∫ y, f (x,y)^2 ∂ν) - (∫ y, f (x,y) ∂ν)^2 ∂μ) := by
    apply integral_congr_ae
    filter_upwards [memLp_two_fiber_ae hf] with x hx
    exact variance_eq_sub hx
  rw [he, integral_sub hf.integrable_sq.integral_prod_left
    (memLp_two_integral_snd hf).integrable_sq, variance_eq_sub hf,
    variance_eq_sub (memLp_two_integral_snd hf)]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hf.integrable_sq, integral_prod _ (hf.integrable one_le_two)]
  ring

lemma variance_integral_le {f : Ω × Ξ → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    Var[fun y => ∫ x, f (x,y) ∂μ; ν] ≤ ∫ x, Var[fun y => f (x,y); ν] ∂μ := by
  let F (x : Ω) := ∫ y, f (x,y) ∂ν
  let g (p : Ω × Ξ) := f p - F p.1
  have hF : MemLp F 2 μ := memLp_two_integral_snd hf
  have hg : MemLp g 2 (μ.prod ν) := hf.sub (hF.comp_fst ν)
  have hgmean : (fun y => ∫ x, g (x,y) ∂μ) =ᵐ[ν]
      (fun y => (∫ x, f (x,y) ∂μ) - ∫ p, f p ∂μ.prod ν) := by
    filter_upwards [(hf.integrable one_le_two).prod_left_ae] with y hy
    dsimp [g]
    rw [integral_sub hy (hF.integrable one_le_two)]
    rw [integral_prod _ (hf.integrable one_le_two)]
  have hineq : (∫ y, (∫ x, g (x,y) ∂μ)^2 ∂ν) ≤
      ∫ y, (∫ x, g (x,y)^2 ∂μ) ∂ν := by
    apply integral_mono_ae (memLp_two_integral_snd (memLp_two_swap hg)).integrable_sq
      hg.integrable_sq.integral_prod_right
    filter_upwards [memLp_two_fiber_ae (memLp_two_swap hg)] with y hy
    exact integral_sq_ge_sq_integral hy
  have hleft : (∫ y, (∫ x, g (x,y) ∂μ)^2 ∂ν) =
      Var[fun y => ∫ x, f (x,y) ∂μ; ν] := by
    rw [variance_eq_integral (memLp_two_integral_snd (memLp_two_swap hf)).aemeasurable]
    have hint : (∫ p, f p ∂μ.prod ν) = ∫ y, ∫ x, f (x,y) ∂μ ∂ν :=
      integral_prod_symm _ (hf.integrable one_le_two)
    apply integral_congr_ae
    filter_upwards [hgmean] with y hy
    rw [hy, hint]
  have hright : (∫ y, (∫ x, g (x,y)^2 ∂μ) ∂ν) =
      ∫ x, Var[fun y => f (x,y); ν] ∂μ := by
    rw [← integral_integral_swap hg.integrable_sq]
    apply integral_congr_ae
    filter_upwards [memLp_two_fiber_ae hf] with x hx
    exact (variance_eq_integral hx.aemeasurable).symm
  rwa [hleft, hright] at hineq

lemma integral_le_const_probability {f : Ω → ℝ} (hf : Integrable f μ) {C : ℝ}
    (h : ∀ x, f x ≤ C) : (∫ x, f x ∂μ) ≤ C := by
  simpa using integral_mono hf (integrable_const C) h

 
def HasRowGrowth {X : Type*} {m : ℕ} (r : X → ℝ) (f : (Fin m → X) → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ a, |f a| ≤ K*(1+∑ i, r (a i))

lemma HasRowGrowth.memLp {X : Type*} [MeasurableSpace X] {m : ℕ}
    {r : X → ℝ} {f : (Fin m → X) → ℝ} (hg : HasRowGrowth r f)
    {a : Ω → Fin m → X} (hf : AEStronglyMeasurable (fun x => f (a x)) μ)
    (hr : ∀ i, MemLp (fun x => r (a x i)) 2 μ) :
    MemLp (fun x => f (a x)) 2 μ := by
  obtain ⟨K, hK, hbound⟩ := hg
  have hh : MemLp (fun x => K*(1+∑ i, r (a x i))) 2 μ :=
    ((memLp_const (1:ℝ)).add (memLp_finsetSum _ (fun i _ => hr i))).const_mul K
  apply hh.mono' hf
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hbound (a x)

lemma HasRowGrowth.cons {X : Type*} {m : ℕ} {r : X → ℝ}
    {f : (Fin (m+1) → X) → ℝ} (hg : HasRowGrowth r f) (hr0 : ∀ x, 0 ≤ r x) (x : X) :
    HasRowGrowth r (fun a => f (Fin.cons x a)) := by
  obtain ⟨K, hK, hbound⟩ := hg
  refine ⟨K*(1+r x), mul_nonneg hK (by linarith [hr0 x]), ?_⟩
  intro a
  have hb := hbound (Fin.cons x a)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hb
  have hs : 0 ≤ ∑ i, r (a i) := Finset.sum_nonneg fun i _ => hr0 (a i)
  nlinarith [mul_nonneg hK (mul_nonneg (hr0 x) hs)]

lemma measurePreserving_cons {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) :
    MeasurePreserving (fun p : X × (Fin m → X) => Fin.cons p.1 p.2)
      (μ.prod (Measure.pi fun _ : Fin m => μ)) (Measure.pi fun _ : Fin (m+1) => μ) := by
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => μ) 0).symm

 

theorem variance_pi_le_of_fiber {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (r : X → ℝ) (hr : MemLp r 2 μ) (hr0 : ∀ x, 0 ≤ r x)
    {m : ℕ} (f : (Fin m → X) → ℝ) (hf : Measurable f) (hg : HasRowGrowth r f)
    (C : ℝ) (hv : ∀ (i : Fin m) (a : Fin m → X),
      Var[fun z => f (Function.update a i z); μ] ≤ C) :
    Var[f; Measure.pi fun _ : Fin m => μ] ≤ (m:ℝ)*C := by
  classical
  induction m with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext a
      congr 1
      funext i
      exact Fin.elim0 i
    rw [he, variance_eq_integral (by fun_prop)]
    simp
  | succ m ih =>
    let H (p : X × (Fin m → X)) := f (Fin.cons p.1 p.2)
    have hHmeas : Measurable H := hf.comp (measurePreserving_cons μ m).measurable
    have hH : MemLp H 2 (μ.prod (Measure.pi fun _ : Fin m => μ)) := by
      apply hg.memLp hHmeas.aestronglyMeasurable
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using hr.comp_fst (Measure.pi fun _ : Fin m => μ)
      · simpa only [Fin.cons_succ, Function.comp_def, Function.eval] using
          (hr.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => μ) j)).comp_snd μ
    have hvar : Var[f; Measure.pi fun _ : Fin (m+1) => μ] = Var[H; μ.prod (Measure.pi fun _ : Fin m => μ)] :=
      ((measurePreserving_cons μ m).variance_fun_comp hf.aemeasurable).symm
    rw [hvar, variance_prod_eq hH]
    have hfirst : (∫ x, Var[fun a => H (x,a); Measure.pi fun _ : Fin m => μ] ∂μ) ≤ (m:ℝ)*C := by
      apply integral_le_const_probability (integrable_fiber_variance hH)
      intro x
      apply ih (fun a => f (Fin.cons x a)) (hf.comp ((measurePreserving_cons μ m).measurable.comp
        (measurable_const.prodMk measurable_id))) (hg.cons hr0 x)
      intro i a
      have he : (fun z => f (Fin.cons x (Function.update a i z))) =
          (fun z => f (Function.update (Fin.cons x a) i.succ z)) := by
        funext z
        rw [Fin.cons_update]
      rw [he]
      exact hv i.succ (Fin.cons x a)
    have hlast : Var[fun x => ∫ a, H (x,a) ∂(Measure.pi fun _ : Fin m => μ); μ] ≤ C := by
      apply (variance_integral_le (memLp_two_swap hH)).trans
      apply integral_le_const_probability (integrable_fiber_variance (memLp_two_swap hH))
      intro a
      have he : (fun x => H (x,a)) =
          (fun x => f (Function.update (Fin.cons (Classical.choice (nonempty_of_isProbabilityMeasure μ)) a) 0 x)) := by
        funext x
        simp only [H, Fin.update_cons_zero]
      rw [he]
      exact hv 0 _
    push_cast
    linarith

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

lemma gaussian_square_memLp_two (v : ℝ≥0) :
    MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have h := (memLp_id_gaussianReal (μ := 0) (v := v) 4).integrable_norm_pow (p := 4) (by norm_num)
  simpa only [id_eq, Real.norm_eq_abs, show (4:ℕ) = 2*2 from rfl, pow_mul, sq_abs] using h

lemma coordinate_square_memLp_two (ε : ℝ) :
    MemLp (fun x : ℝ => x^2) 2 (coordinateLaw ε) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  exact ((gaussian_square_memLp_two (Real.toNNReal (1-ε))).integrable_sq.smul_measure
    (by norm_num)).add_measure ((gaussian_square_memLp_two (Real.toNNReal (1+ε))).integrable_sq.smul_measure
      (by norm_num))

def rowNormSq {n : ℕ} (a : Fin n → ℝ) : ℝ := ∑ i, (a i)^2

lemma rowNormSq_nonneg {n : ℕ} (a : Fin n → ℝ) : 0 ≤ rowNormSq a :=
  Finset.sum_nonneg fun i _ => sq_nonneg (a i)

lemma rowNormSq_memLp_two (n : ℕ) (ε : ℝ) :
    MemLp (@rowNormSq n) 2 (Measure.pi fun _ : Fin n => coordinateLaw ε) := by
  apply memLp_finsetSum
  intro i _
  exact (coordinate_square_memLp_two ε).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => coordinateLaw ε) i)

lemma gaussian_potential_sq_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ => (potential x)^2) (gaussianReal 0 v) := by
  have hc : MemLp (fun _ : ℝ => (1:ℝ)) 2 (gaussianReal 0 v) := memLp_const 1
  have h : MemLp (fun x : ℝ => 1+x^2) 2 (gaussianReal 0 v) :=
    hc.add (gaussian_square_memLp_two v)
  apply (h.mono' (by unfold potential; fun_prop) ?_).integrable_sq
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (potential_nonneg x)] using potential_le_quadratic x

def cavityMomentConstant : ℝ := ∫ x : ℝ, (1+2*x^2)^2 ∂gaussianReal 0 1

lemma cavityMoment_integrable : Integrable (fun x : ℝ => (1+2*x^2)^2) (gaussianReal 0 1) := by
  have hc : MemLp (fun _ : ℝ => (1:ℝ)) 2 (gaussianReal 0 1) := memLp_const 1
  exact (hc.add ((gaussian_square_memLp_two 1).const_mul 2)).integrable_sq

lemma cavityMomentConstant_nonneg : 0 ≤ cavityMomentConstant :=
  integral_nonneg fun _ => sq_nonneg _

lemma gaussian_potential_sq_bound {v : ℝ≥0} (hv : (v:ℝ) ≤ 2) :
    (∫ x : ℝ, (potential x)^2 ∂gaussianReal 0 v) ≤ cavityMomentConstant := by
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt v*x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp
  rw [← hmap, integral_map (by fun_prop) (by unfold potential; fun_prop)]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    cavityMoment_integrable
  filter_upwards [] with x
  have hp := potential_le_quadratic (Real.sqrt v*x)
  have hp0 := potential_nonneg (Real.sqrt v*x)
  have hvx : (Real.sqrt (v:ℝ)*x)^2 ≤ 2*x^2 := by
    rw [mul_pow]
    have hs : Real.sqrt (v:ℝ)^2 = (v:ℝ) := Real.sq_sqrt (NNReal.coe_nonneg v)
    rw [hs]
    exact mul_le_mul_of_nonneg_right hv (sq_nonneg x)
  nlinarith [sq_nonneg x]

lemma varianceMark_upper {ε : ℝ} (he : ε ∈ Set.Icc (0:ℝ) (1/2)) (b : Bool) :
    (varianceMark ε b : ℝ) ≤ 2 := by
  cases b <;> simp only [varianceMark, Bool.false_eq_true, ↓reduceIte, Real.coe_toNNReal'] <;>
    exact max_le (by linarith [he.1, he.2]) (by norm_num)

lemma projected_potential_sq_bound {n : ℕ} {ε : ℝ} (he : ε ∈ Set.Icc (0:ℝ) (1/2))
    (y : EuclideanSpace ℝ (Fin n)) (hy : ‖y‖ = 1) :
    (∫ a : Fin n → ℝ, (potential (∑ i, y i*a i))^2
      ∂(Measure.pi fun _ => coordinateLaw ε)) ≤ cavityMomentConstant := by
  classical
  let v (σ : Fin n → Bool) : ℝ≥0 :=
    ∑ i, NNReal.mk ((y i)^2) (sq_nonneg (y i)) * varianceMark ε (σ i)
  have hv (σ) : (v σ : ℝ) ≤ 2 := by
    dsimp [v]
    simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk]
    calc
      _ ≤ ∑ i, (y i)^2*2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (varianceMark_upper he _) (sq_nonneg _)
      _ = 2 := by rw [← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq, hy]; norm_num
  have hm : Measurable (fun a : Fin n → ℝ => ∑ i, y i*a i) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))
  have hproj (σ : Fin n → Bool) := gaussian_projection (fun i => varianceMark ε (σ i)) (fun i => y i)
  have hInt (σ : Fin n → Bool) : Integrable (fun a : Fin n → ℝ => (potential (∑ i, y i*a i))^2)
      (Measure.pi fun i => gaussianReal 0 (varianceMark ε (σ i))) := by
    have hi := gaussian_potential_sq_integrable (v σ)
    rw [← hproj] at hi
    exact (integrable_map_measure (by unfold potential; fun_prop) hm.aemeasurable).mp hi
  rw [product_mixture_expansion, integral_finsetSum_measure]
  · simp only [integral_smul_measure, smul_eq_mul, Fintype.card_fin]
    calc
      _ ≤ ∑ σ : Fin n → Bool, ((1/2:ℝ≥0∞)^n).toReal*cavityMomentConstant := by
        apply Finset.sum_le_sum
        intro σ _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        rw [← integral_map (f := fun x : ℝ => (potential x)^2) hm.aemeasurable
          (by unfold potential; fun_prop), hproj]
        exact gaussian_potential_sq_bound (hv σ)
      _ = cavityMomentConstant := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_pow,
          ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
        rw [← mul_assoc, ← mul_pow]
        norm_num
  · intro σ _
    exact (hInt σ).smul_measure (by finiteness)

lemma potential_row_bound {n : ℕ} (a : Fin n → ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ = 1) : potential (∑ i, a i*y i) ≤ 1+rowNormSq a := by
  apply (potential_le_quadratic _).trans
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun i => y i)
  rw [← EuclideanSpace.real_norm_sq_eq y, hy] at h
  simpa only [one_pow, mul_one, rowNormSq] using add_le_add_right h 1

lemma unitGround_rowGrowth {m n : ℕ} (hn : 0 < n) :
    HasRowGrowth (@rowNormSq n) (@unitGround m n) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨y, hy⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin n)) (show (0:ℝ) ≤ 1 by norm_num)
  refine ⟨(m:ℝ)+1, by positivity, ?_⟩
  intro A
  rw [abs_of_nonneg (unitGround_nonneg hn A)]
  apply (unitGround_le hn A hy).trans
  calc
    unitEnergy A y ≤ ∑ j, (1+rowNormSq (A j)) :=
      Finset.sum_le_sum fun j _ => potential_row_bound (A j) hy
    _ = (m:ℝ)+∑ j, rowNormSq (A j) := by simp [Finset.sum_add_distrib]
    _ ≤ ((m:ℝ)+1)*(1+∑ j, rowNormSq (A j)) := by
      have hsum : 0 ≤ ∑ j, rowNormSq (A j) := Finset.sum_nonneg fun j _ => rowNormSq_nonneg _
      nlinarith [Nat.cast_nonneg (α := ℝ) m]

lemma unitEnergy_update {m n : ℕ} (A : Fin m → Fin n → ℝ) (j : Fin m)
    (z : Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    unitEnergy (Function.update A j z) y = unitEnergy (Function.update A j 0) y +
      potential (∑ i, z i*y i) := by
  classical
  unfold unitEnergy
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  have hp : potential 0 = 0 := by norm_num [potential]
  rw [hp, zero_add]
  have he : (∑ k ∈ Finset.univ.erase j, potential (∑ i, Function.update A j z k i*y i)) =
      ∑ k ∈ Finset.univ.erase j, potential (∑ i, Function.update A j 0 k i*y i) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [he, add_comm]

lemma unitGround_update_lower {m n : ℕ} (hn : 0 < n) (A : Fin m → Fin n → ℝ)
    (j : Fin m) (z : Fin n → ℝ) :
    unitGround (Function.update A j 0) ≤ unitGround (Function.update A j z) := by
  obtain ⟨y, hy, he, _⟩ := unitGround_attained hn (Function.update A j z)
  rw [he, unitEnergy_update]
  exact (unitGround_le hn _ hy).trans (le_add_of_nonneg_right (potential_nonneg _))

lemma unitGround_cavity_upper {m n : ℕ} (hn : 0 < n) (A : Fin m → Fin n → ℝ)
    (j : Fin m) : ∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 ∧ ∀ z : Fin n → ℝ,
      unitGround (Function.update A j z) - unitGround (Function.update A j 0) ≤
        potential (∑ i, z i*y i) := by
  obtain ⟨y, hy, he, _⟩ := unitGround_attained hn (Function.update A j 0)
  refine ⟨y, hy, fun z => ?_⟩
  have h := unitGround_le hn (Function.update A j z) hy
  rw [unitEnergy_update, ← he] at h
  linarith

lemma memLp_unitGround_update {m n : ℕ} (hn : 0 < n) (ε : ℝ)
    (A : Fin m → Fin n → ℝ) (j : Fin m) :
    MemLp (fun z => unitGround (Function.update A j z)) 2
      (Measure.pi fun _ : Fin n => coordinateLaw ε) := by
  classical
  apply (unitGround_rowGrowth hn).memLp
  · apply Continuous.aestronglyMeasurable
    apply continuous_unitGround.comp
    exact continuous_pi (fun k => by
      by_cases h : k = j
      · simp only [h, Function.update_self]
        exact continuous_id
      · simp only [Function.update_of_ne h]
        exact continuous_const)
  · intro k
    by_cases h : k = j
    · simpa [h] using rowNormSq_memLp_two n ε
    · simpa [Function.update_of_ne h] using
        (memLp_const (rowNormSq (A k)) : MemLp (fun _ : Fin n → ℝ => rowNormSq (A k)) 2
          (Measure.pi fun _ : Fin n => coordinateLaw ε))

lemma variance_unitGround_fiber {m n : ℕ} (hn : 0 < n) {ε : ℝ}
    (he : ε ∈ Set.Icc (0:ℝ) (1/2)) (A : Fin m → Fin n → ℝ) (j : Fin m) :
    Var[fun z => unitGround (Function.update A j z);
      Measure.pi fun _ : Fin n => coordinateLaw ε] ≤ cavityMomentConstant := by
  let μ := Measure.pi fun _ : Fin n => coordinateLaw ε
  have hf := memLp_unitGround_update hn ε A j
  obtain ⟨y, hy, hupper⟩ := unitGround_cavity_upper hn A j
  rw [← variance_sub_const hf.aestronglyMeasurable (unitGround (Function.update A j 0))]
  apply (variance_le_expectation_sq (hf.sub (memLp_const _)).aestronglyMeasurable).trans
  apply le_trans _ (projected_potential_sq_bound he y hy)
  have hproj : Integrable (fun z : Fin n → ℝ => (potential (∑ i, y i*z i))^2) μ := by
    
    have hc : MemLp (fun _ : Fin n → ℝ => (1:ℝ)) 2 μ := memLp_const 1
    have hh : MemLp (fun z : Fin n → ℝ => 1+rowNormSq z) 2 μ :=
      hc.add (rowNormSq_memLp_two n ε)
    have hmeas : Measurable (fun z : Fin n → ℝ => potential (∑ i, y i*z i)) := by
      unfold potential
      exact measurable_const.mul (((measurable_const.sub
        (Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i)))).max
        measurable_const).pow_const 2)
    apply (hh.mono' hmeas.aestronglyMeasurable ?_).integrable_sq
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (potential_nonneg _)]
    simpa only [mul_comm] using potential_row_bound z hy
  apply integral_mono (hf.sub (memLp_const _)).integrable_sq hproj
  intro z
  have hl := unitGround_update_lower hn A j z
  have hu := hupper z
  have hp := potential_nonneg (∑ i, z i*y i)
  simpa only [Pi.sub_apply, mul_comm] using pow_le_pow_left₀ (sub_nonneg.mpr hl) hu 2

 
theorem variance_unitGround_le_rows {m n : ℕ} (hn : 0 < n) {ε : ℝ}
    (he : ε ∈ Set.Icc (0:ℝ) (1/2)) :
    Var[@unitGround m n; Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε]
      ≤ (m:ℝ)*cavityMomentConstant := by
  apply variance_pi_le_of_fiber _ (@rowNormSq n) (rowNormSq_memLp_two n ε)
    rowNormSq_nonneg _ continuous_unitGround.measurable (unitGround_rowGrowth hn)
  intro j A
  exact variance_unitGround_fiber hn he A j

lemma memLp_unitGround {m n : ℕ} (hn : 0 < n) (ε : ℝ) :
    MemLp (@unitGround m n) 2
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε) := by
  apply (unitGround_rowGrowth hn).memLp continuous_unitGround.aestronglyMeasurable
  intro i
  exact (rowNormSq_memLp_two n ε).comp_measurePreserving (measurePreserving_eval _ i)

lemma satProbability_le_variance_bound {α ε e : ℝ} {n : ℕ} (hn : 0 < n)
    (ha : 0 < α) (he : ε ∈ Set.Icc (0:ℝ) (1/2)) (hepos : 0 < e)
    (hmean : e/2*(n:ℝ) ≤ ∫ A, groundEnergy A ∂disorderLaw ε α n) :
    satProbability ε α n ≤ (4*α*cavityMomentConstant/e^2)/(n:ℝ) := by
  let μ := disorderLaw ε α n
  have : IsProbabilityMeasure μ := by dsimp [μ, disorderLaw]; infer_instance
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hf : MemLp (fun A : PatternMatrix α n => groundEnergy A) 2 μ := by
    simpa only [groundEnergy_eq_unitGround hn, μ, disorderLaw] using memLp_unitGround (m := rowCount α n) hn ε
  have hv : Var[fun A : PatternMatrix α n => groundEnergy A; μ] ≤
      (rowCount α n:ℝ)*cavityMomentConstant := by
    simpa only [groundEnergy_eq_unitGround hn, μ, disorderLaw] using
      variance_unitGround_le_rows (m := rowCount α n) hn he
  have hc : 0 < e/2*(n:ℝ) := by positivity
  have hs : μ {A | satisfiable A} ≤
      ENNReal.ofReal (Var[fun A : PatternMatrix α n => groundEnergy A; μ] / (e/2*n)^2) := by
    apply le_trans (measure_mono (show {A | satisfiable A} ⊆
      {A | e/2*(n:ℝ) ≤ |groundEnergy A - ∫ B, groundEnergy B ∂μ|} from ?_))
      (meas_ge_le_variance_div_sq hf hc)
    intro A hA
    have hzero : groundEnergy A = 0 := by
      rw [groundEnergy_eq_unitGround hn]
      exact (unitSatisfiable_iff_ground hn A).mp ((satisfiable_iff_unit hn A).mp hA)
    change e/2*(n:ℝ) ≤ |groundEnergy A - ∫ B, groundEnergy B ∂μ|
    rw [hzero, zero_sub, abs_neg, abs_of_nonneg (hc.le.trans hmean)]
    exact hmean
  have hsreal := ENNReal.toReal_le_of_le_ofReal
    (div_nonneg (variance_nonneg _ _) (sq_nonneg _)) hs
  apply hsreal.trans
  calc
    _ ≤ ((rowCount α n:ℝ)*cavityMomentConstant)/(e/2*n)^2 :=
      div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ ≤ (α*n*cavityMomentConstant)/(e/2*n)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) cavityMomentConstant_nonneg
    _ = (4*α*cavityMomentConstant/e^2)/(n:ℝ) := by
      field_simp
      ring

 
def PositiveEnergyUnsatStatement : Prop :=
  ∀ α ε e : ℝ, 0 < α → 0 ≤ ε → ε ≤ 1/2 → 0 < e →
    Tendsto (fun N : ℕ =>
      (∫ A, groundEnergy A ∂disorderLaw ε α N) / (N : ℝ)) atTop (𝓝 e) →
    Tendsto (satProbability ε α) atTop (𝓝 0)

 

theorem positive_energy_implies_unsat : PositiveEnergyUnsatStatement := by
  intro α ε e ha he0 he1 hepos henergy
  have hmean : ∀ᶠ n : ℕ in atTop,
      e/2 < (∫ A, groundEnergy A ∂disorderLaw ε α n)/(n:ℝ) :=
    henergy.eventually_const_lt (by linarith)
  have hbound : ∀ᶠ n : ℕ in atTop,
      satProbability ε α n ≤ (4*α*cavityMomentConstant/e^2)/(n:ℝ) := by
    filter_upwards [hmean, eventually_gt_atTop (0:ℕ)] with n hm hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    exact satProbability_le_variance_bound hn ha ⟨he0, he1⟩ hepos
      (le_of_lt ((lt_div_iff₀ hnpos).mp hm))
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound
    (tendsto_const_div_atTop_nhds_zero_nat _)

end MicroscopicJamming

end

end OAI
