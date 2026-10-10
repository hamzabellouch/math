import Mathlib
import OAI.Probability.SKBarriers.Coverage.CoverageScale
import OAI.Probability.SKBarriers.Dynamics.GreedyNumerics

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem high_probability_inter (C D : (n : ℕ) → Set (Disorder n))
    (hD : ∀n,MeasurableSet (D n))
    (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (hD1 : Tendsto (fun n => (disorderLaw n).real (D n)) atTop (𝓝 1)) :
    Tendsto (fun n => (disorderLaw n).real (C n ∩ D n)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g:=fun n => (disorderLaw n).real (C n)+(disorderLaw n).real (D n)-1)
    (h:=fun _ => (1:ℝ))
  · convert (hC1.add hD1).sub_const 1 using 1; norm_num
  · exact tendsto_const_nhds
  · intro n
    have H := measureReal_union_add_inter (μ:=disorderLaw n) (s:=C n) (hD n)
    have H1 : (disorderLaw n).real (C n ∪ D n)≤1 := measureReal_le_one
    linarith only [H,H1]
  · intro n; exact measureReal_le_one

def finiteGoodEvent (C : ℕ → (n : ℕ) → Set (Disorder n)) : ℕ → (n : ℕ) → Set (Disorder n)
  | 0,_ => univ
  | j+1,n => finiteGoodEvent C j n ∩ C j n

 theorem finiteGoodEvent_mem (C : ℕ → (n : ℕ) → Set (Disorder n)) (B n : ℕ) (J : Disorder n) :
    J∈finiteGoodEvent C B n ↔ ∀j<B,J∈C j n := by
  induction B with
  | zero => simp [finiteGoodEvent]
  | succ B ih =>
    simp only [finiteGoodEvent,mem_inter_iff,ih]
    constructor
    · rintro ⟨h,hB⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj|rfl
      · exact h j hj
      · exact hB
    · intro h; exact ⟨fun j hj => h j (by omega),h B (by omega)⟩

 theorem finiteGoodEvent_measurable (C : ℕ → (n : ℕ) → Set (Disorder n))
    (hC : ∀j n,MeasurableSet (C j n)) (B n : ℕ) : MeasurableSet (finiteGoodEvent C B n) := by
  induction B with
  | zero => exact MeasurableSet.univ
  | succ B ih => exact ih.inter (hC B n)

 theorem finiteGoodEvent_tendsto (C : ℕ → (n : ℕ) → Set (Disorder n))
    (hC : ∀j n,MeasurableSet (C j n))
    (hC1 : ∀j,Tendsto (fun n => (disorderLaw n).real (C j n)) atTop (𝓝 1)) (B : ℕ) :
    Tendsto (fun n => (disorderLaw n).real (finiteGoodEvent C B n)) atTop (𝓝 1) := by
  induction B with
  | zero => simpa only [finiteGoodEvent,probReal_univ] using (tendsto_const_nhds (x:=(1:ℝ)))
  | succ B ih => exact high_probability_inter _ _ (hC B) ih (hC1 B)

 theorem real_markov_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hm : Measurable f) (h0 : ∀x,0≤f x)
    {a : ℝ} (ha : 0<a) : μ.real {x | a<f x}≤(∫x,f x ∂μ)/a := by
  have hA : MeasurableSet {x | a<f x} := measurableSet_lt measurable_const hm
  apply (le_div_iff₀ ha).mpr
  have H : (∫x,({x | a<f x}).indicator (fun _ => a) x ∂μ)≤∫x,f x ∂μ := by
    apply integral_mono ((integrable_const a).indicator hA) hf
    intro x
    by_cases hx : a<f x
    · simpa only [Set.indicator_of_mem (show x∈{x | a<f x} from hx)] using hx.le
    · simpa only [Set.indicator_of_notMem (show x∉{x | a<f x} from hx)] using h0 x
  simpa only [integral_indicator_const _ hA,smul_eq_mul,mul_comm] using H

 theorem stretched_exp_decay {c : ℝ} (hc : 0<c) :
    Tendsto (fun n => Real.exp (-c*levelLogScale n)) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp (stretchedLogScale_tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hc))

 theorem faster_stretched_decay {u : ℝ} (hu : kappa<u) (A K : ℝ) :
    Tendsto (fun n : ℕ => K*Real.exp (A*levelLogScale n-(n:ℝ)^u)) atTop (𝓝 0) := by
  have hu0 : 0<u := (by norm_num [kappa] : (0:ℝ)<kappa).trans hu
  have H : Tendsto (fun n : ℕ => Real.exp (-(1/2:ℝ)*(n:ℝ)^u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (((tendsto_rpow_atTop hu0).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul_atTop_of_neg (by norm_num))
  have H0 : Tendsto (fun n : ℕ => Real.exp (A*levelLogScale n-(n:ℝ)^u)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => (Real.exp_pos _).le)) _ H
    filter_upwards [eventually_const_rpow_le hu A (by norm_num : (0:ℝ)<1/2)] with n hn
    apply Real.exp_le_exp.mpr
    change A*(n:ℝ)^kappa-(n:ℝ)^u≤-(1/2:ℝ)*(n:ℝ)^u
    linarith only [hn]
  simpa only [mul_zero] using H0.const_mul K

 theorem high_probability_small_replica {d : ℕ} (β : ℝ) (S : (n : ℕ) → Finset (ReplicaConfig n d))
    {u : ℝ} (hu : kappa<u) (K A : ℝ)
    (h : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (S n) ∂disorderLaw n)≤K*Real.exp (-(n:ℝ)^u)) :
    Tendsto (fun n => (disorderLaw n).real {J | replicaGibbsMass β J (S n)≤Real.exp (-A*levelLogScale n)}) atTop (𝓝 1) := by
  have HC : Tendsto (fun n => (disorderLaw n).real {J | Real.exp (-A*levelLogScale n)<replicaGibbsMass β J (S n)}) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) _ (faster_stretched_decay hu A K)
    filter_upwards [h] with n hn
    refine (real_markov_bound (disorderLaw n) (replicaGibbsMass_integrable β (S n))
      (continuous_replicaGibbsMass β (S n)).measurable (fun J => replicaGibbsMass_nonneg β J (S n)) (Real.exp_pos _)).trans ?_
    calc
      _ ≤ (K*Real.exp (-(n:ℝ)^u))/Real.exp (-A*levelLogScale n) := div_le_div_of_nonneg_right hn (Real.exp_pos _).le
      _ = K*Real.exp (A*levelLogScale n-(n:ℝ)^u) := by rw [mul_div_assoc,← Real.exp_sub]; congr 2; ring
  have H := (tendsto_const_nhds (x:=(1:ℝ))).sub HC
  convert H using 1
  · funext n
    have hM : MeasurableSet {J | Real.exp (-A*levelLogScale n)<replicaGibbsMass β J (S n)} :=
      measurableSet_lt measurable_const (continuous_replicaGibbsMass β (S n)).measurable
    rw [← probReal_compl_eq_one_sub hM]
    congr 1
    ext J
    simp only [mem_ofPred_eq,mem_compl_iff,not_lt]
  · norm_num

end SK.Analytic

end
end

end OAI
