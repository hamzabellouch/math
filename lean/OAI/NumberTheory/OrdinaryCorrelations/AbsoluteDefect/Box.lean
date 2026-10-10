import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set

namespace OrdinaryCauchyTail

def box (t : ℝ) : ℝ := (Icc (-1:ℝ) 1).indicator (fun _ => 1) t

def cauchy (t : ℝ) : ℝ := (1+t^2)⁻¹

def tailWeight (R t : ℝ) : ℝ := {t : ℝ | R < |t|}.indicator cauchy t

lemma box_nonneg (t : ℝ) : 0≤box t := Set.indicator_nonneg (fun _ _ => zero_le_one) t
lemma box_integrable : Integrable box := by
  exact (integrableOn_const (C:=(1:ℝ)) (isCompact_Icc.measure_lt_top.ne)).integrable_indicator measurableSet_Icc
lemma cauchy_nonneg (t : ℝ) : 0≤cauchy t := by unfold cauchy; positivity
lemma cauchy_integrable : Integrable cauchy := integrable_inv_one_add_sq
lemma measurable_tail (R : ℝ) : MeasurableSet {t : ℝ | R < |t|} := isOpen_lt continuous_const continuous_abs |>.measurableSet
lemma tail_nonneg (R t : ℝ) : 0≤tailWeight R t := Set.indicator_nonneg (fun t _ => cauchy_nonneg t) t
lemma tail_integrable (R : ℝ) : Integrable (tailWeight R) := cauchy_integrable.indicator (measurable_tail R)

lemma box_shift_integral (g : ℝ → ℝ) (u : ℝ) :
    (∫ t : ℝ, box (t-u)*g t) = ∫ t in Icc (-1:ℝ) 1, g (t+u) := by
  calc
    _ = ∫ t : ℝ, box ((t+u)-u)*g (t+u) := (integral_add_right_eq_self _ u).symm
    _ = ∫ t : ℝ, (Icc (-1:ℝ) 1).indicator (fun t => g (t+u)) t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by by_cases ht : t∈Icc (-1:ℝ) 1 <;> simp [box,ht])
    _ = _ := integral_indicator measurableSet_Icc

lemma box_reflect_integral (w : ℝ → ℝ) (t : ℝ) :
    (∫ u : ℝ, w u*box (t-u)) = ∫ v in Icc (-1:ℝ) 1, w (t-v) := by
  calc
    _ = ∫ v : ℝ, w (t-v)*box (t-(t-v)) := (integral_sub_left_eq_self _ volume t).symm
    _ = ∫ v : ℝ, (Icc (-1:ℝ) 1).indicator (fun v => w (t-v)) v := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v => by by_cases hv : v∈Icc (-1:ℝ) 1 <;> simp [box,hv])
    _ = _ := integral_indicator measurableSet_Icc

lemma cauchy_close (t v : ℝ) (hv : v∈Icc (-1:ℝ) 1) : cauchy t≤3*cauchy (t-v) := by
  have hv2 : v^2≤1 := by nlinarith [hv.1,hv.2]
  have hden : 1+(t-v)^2≤3*(1+t^2) := by nlinarith [sq_nonneg (t+v),sq_nonneg t]
  unfold cauchy
  have hh : 1/(1+t^2)≤3/(1+(t-v)^2) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa using hden)
  simpa only [div_eq_mul_inv,one_mul] using hh

lemma tail_close (R t v : ℝ) (hv : v∈Icc (-1:ℝ) 1) :
    tailWeight (R+1) t≤3*tailWeight R (t-v) := by
  by_cases ht : R+1 < |t|
  · have hv1 : |v|≤1 := abs_le.mpr hv
    have hh : R < |t-v| := by
      have hab := abs_add_le (t-v) v
      rw [sub_add_cancel] at hab
      linarith
    simpa [tailWeight,ht,hh] using cauchy_close t v hv
  · have he : tailWeight (R+1) t=0 := by simp [tailWeight,ht]
    rw [he]
    exact mul_nonneg (by norm_num) (tail_nonneg R (t-v))

lemma tail_convolution_lower (R t : ℝ) :
    2*tailWeight (R+1) t≤3*(∫ u : ℝ, tailWeight R u*box (t-u)) := by
  rw [box_reflect_integral]
  have hti : IntegrableOn (fun v : ℝ => tailWeight R (t-v)) (Icc (-1:ℝ) 1) :=
    ((tail_integrable R).comp_sub_left t).integrableOn
  have hc : IntegrableOn (fun _ : ℝ => tailWeight (R+1) t) (Icc (-1:ℝ) 1) :=
    integrableOn_const (isCompact_Icc.measure_lt_top.ne)
  have hh := integral_mono_ae hc (hti.const_mul 3)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv; exact tail_close R t v hv)
  norm_num [integral_const_mul,integral_const,Measure.real,Measure.restrict_apply,Real.volume_Icc] at hh
  exact hh

theorem tail_bound {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀t, 0≤g t)
    {B K : ℝ} (hB : ∀t, ‖g t‖≤B)
    (hK : ∀u, (∫t in Icc (-1:ℝ) 1, g (t+u))≤K) (R : ℝ) :
    (∫ t : ℝ, tailWeight (R+1) t*g t) ≤ (3/2)*K*(∫u : ℝ, tailWeight R u) := by
  let H : ℝ×ℝ → ℝ := fun p => tailWeight R p.2*box (p.1-p.2)*g p.1
  have hi0 : Integrable (fun p : ℝ×ℝ => tailWeight R p.2*box (p.1-p.2)) (volume.prod volume) :=
    (tail_integrable R).convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) box_integrable
  have hi : Integrable H (volume.prod volume) :=
    hi0.mul_bdd (hg.comp continuous_fst).aestronglyMeasurable (Filter.Eventually.of_forall (fun p => hB p.1))
  have he (t : ℝ) : (∫u : ℝ, H (t,u)) = (∫u : ℝ, tailWeight R u*box (t-u))*g t := by
    change (∫u : ℝ, (tailWeight R u*box (t-u))*g t) = _
    exact integral_mul_const _ _
  have hs (u : ℝ) : (∫t : ℝ, H (t,u)) = tailWeight R u*(∫t in Icc (-1:ℝ) 1, g (t+u)) := by
    simp only [H,mul_assoc,integral_const_mul,box_shift_integral]
  have hsmall := (tail_integrable (R+1)).mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have h1 : 2*(∫t : ℝ, tailWeight (R+1) t*g t) ≤ 3*(∫t : ℝ, ∫u : ℝ, H (t,u)) := by
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_mono (hsmall.const_mul 2) (hi.integral_prod_left.const_mul 3)
    intro t
    dsimp only
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right (tail_convolution_lower R t) (hg0 t)]
  have h2 : (∫t : ℝ, ∫u : ℝ, H (t,u)) ≤ K*(∫u : ℝ, tailWeight R u) := by
    rw [integral_integral_swap hi,←integral_const_mul]
    apply integral_mono hi.integral_prod_right ((tail_integrable R).const_mul K)
    intro u
    dsimp only
    rw [hs]
    nlinarith [mul_le_mul_of_nonneg_left (hK u) (tail_nonneg R u)]
  linarith

lemma tendsto_tail_integral : Filter.Tendsto (fun R : ℝ => ∫t : ℝ, tailWeight R t)
    Filter.atTop (nhds 0) := by
  have hh := tendsto_integral_filter_of_dominated_convergence
    («μ» := volume) (l:=Filter.atTop) (F:=tailWeight) (f:=fun _ : ℝ => (0:ℝ)) cauchy
    (Filter.Eventually.of_forall (fun R => (tail_integrable R).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun R => Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (tail_nonneg R t)]
      by_cases ht : R < |t|
      · simp [tailWeight,ht]
      · simp [tailWeight,ht,cauchy_nonneg]))) cauchy_integrable
    (Filter.Eventually.of_forall (fun t => by
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop |t|] with R hR
      simp [tailWeight,not_lt.mpr hR]))
  simpa using hh

lemma cauchy_le_one (t : ℝ) : cauchy t≤1 := by
  unfold cauchy
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])

lemma tail_decomposition {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ}
    (hB : ∀t, ‖g t‖≤B) (R : ℝ) :
    (∫t : ℝ, cauchy t*g t) = (∫t in Icc (-R) R, cauchy t*g t) +
      (∫t : ℝ, tailWeight R t*g t) := by
  have hi := cauchy_integrable.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hset : {t : ℝ | R < |t|} = (Icc (-R) R)ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,Set.mem_Icc,←abs_le,not_le]
  have he : (fun t => tailWeight R t*g t) = (Icc (-R) R)ᶜ.indicator (fun t => cauchy t*g t) := by
    funext t
    unfold tailWeight
    rw [hset]
    by_cases ht : t∈(Icc (-R) R)ᶜ <;> simp [ht]
  rw [he,integral_indicator measurableSet_Icc.compl]
  exact (integral_add_compl measurableSet_Icc hi).symm

theorem small_of_compact {g : ℝ → ℝ → ℝ} {K : ℝ} (hK0 : 0≤K)
    (hg : ∀δ, 0<δ → Continuous (g δ)) (hg0 : ∀δ t, 0<δ → 0≤g δ t)
    (hbounded : ∀δ, 0<δ → ∃B, ∀t, ‖g δ t‖≤B)
    (hlocal : ∀δ, 0<δ → δ≤1 → ∀u, (∫t in Icc (-1:ℝ) 1, g δ (t+u))≤K)
    (hcompact : ∀T ζ : ℝ, 0<ζ → ∃η : ℝ, 0<η ∧ ∀δ : ℝ,
      0<δ → δ≤η → (∫t in Icc (-T) T, g δ t)≤ζ) :
    ∀ζ : ℝ, 0<ζ → ∃η : ℝ, 0<η ∧ ∀δ : ℝ,
      0<δ → δ≤η → (∫t : ℝ, cauchy t*g δ t)≤ζ := by
  intro ζ hζ
  have heps : 0<ζ/(3*(K+1)) := by positivity
  have he := tendsto_tail_integral.eventually (eventually_lt_nhds heps)
  obtain ⟨R,hR,hRi⟩ := (he.and (Filter.eventually_ge_atTop (1:ℝ))).exists
  obtain ⟨η,hη,hsmall⟩ := hcompact (R+1) (ζ/2) (by positivity)
  refine ⟨min η 1,lt_min hη zero_lt_one,?_⟩
  intro δ hδ hδη
  obtain ⟨B,hB⟩ := hbounded δ hδ
  have htail := tail_bound (hg δ hδ) (fun t => hg0 δ t hδ) hB (hlocal δ hδ (hδη.trans (min_le_right _ _))) R
  have htail0 : 0≤∫u : ℝ, tailWeight R u := integral_nonneg (tail_nonneg R)
  have htail' : (∫t : ℝ, tailWeight (R+1) t*g δ t)≤ζ/2 := by
    have hh := (lt_div_iff₀ (by positivity : (0:ℝ)<3*(K+1))).mp hR
    nlinarith
  have hi := ((hg δ hδ).continuousOn.integrableOn_Icc : IntegrableOn (g δ) (Icc (-(R+1)) (R+1)))
  have hci := (cauchy_integrable.mul_bdd (hg δ hδ).aestronglyMeasurable
    (Filter.Eventually.of_forall hB)).integrableOn (s:=Icc (-(R+1)) (R+1))
  have hc : (∫t in Icc (-(R+1)) (R+1), cauchy t*g δ t)≤ζ/2 := by
    apply (integral_mono_ae hci hi _).trans (hsmall δ hδ (hδη.trans (min_le_left _ _)))
    exact Filter.Eventually.of_forall (fun t => by nlinarith [mul_le_mul_of_nonneg_right (cauchy_le_one t) (hg0 δ t hδ)])
  rw [tail_decomposition (hg δ hδ) hB (R+1)]
  linarith

end OrdinaryCauchyTail

end

end OAI
