import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetMeasurable

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def stageEndpointMass {d k : ℕ} (e f : Direction d) (a G : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (h : ℕ) (ω : Environment d) : ℝ≥0∞ :=
  rawTupleMixture (realPosition (step e)) h (π ω).val ω {y | TupleSeparated f G y}

lemma stageEndpointMass_adapted {d k : ℕ} (e f : Direction d) (a G : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    Adapted (rowHeightFiltration (realPosition (step e)) a) (stageEndpointMass e f a G π) := by
  intro h
  have hle : rowSigma (BelowHeight (realPosition (step e)) a) ≤
      rowSigma (BelowHeight (realPosition (step e)) (a+h)) := by
    apply rowSigma_mono
    intro y hy
    change dot (realPosition y) (realPosition (step e)) < a+h
    change dot (realPosition y) (realPosition (step e)) < a at hy
    linarith [Nat.cast_nonneg (α:=ℝ) h]
  have hp := ((LayerTupleProfile.measurable_toSupported e a).comp hπ).mono hle le_rfl
  have hm := (rawTupleMixture_joint_rows (realPosition (step e)) h
    (TupleAtHeight (k:=k) (realPosition (step e)) a)
    (BelowHeight (realPosition (step e)) (a+h)) (by
      intro x hx j y hy
      change dot (realPosition y) (realPosition (step e))<a+h
      simpa only [hx j] using hy.2)).comp (hp.prodMk measurable_id)
  exact (Measure.measurable_coe (Set.to_countable _).measurableSet).comp hm

noncomputable def stageTestMass {d k : ℕ} (e f : Direction d) (a Gminus Gplus : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H h : ℕ) (ω : Environment d) : ℝ≥0∞ :=
  if h=0 then 1 else if h=H then
    min (stageEndpointMass e f a Gminus π h ω) (stageEndpointMass e f a Gplus π h ω)
  else stageEndpointMass e f a Gminus π h ω

lemma stageTestMass_adapted {d k : ℕ} (e f : Direction d) (a Gminus Gplus : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) (H : ℕ) :
    Adapted (rowHeightFiltration (realPosition (step e)) a) (stageTestMass e f a Gminus Gplus π H) := by
  intro h
  change @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+h))) _
    (fun ω => stageTestMass e f a Gminus Gplus π H h ω)
  by_cases hh : h=0
  · simp only [stageTestMass,hh]; exact measurable_const
  · simp only [stageTestMass,ite_eq_right hh]
    by_cases hH : h=H
    · simp only [ite_eq_left hH]
      exact (stageEndpointMass_adapted e f a Gminus π hπ h).min
        (stageEndpointMass_adapted e f a Gplus π hπ h)
    · simp only [ite_eq_right hH]
      exact stageEndpointMass_adapted e f a Gminus π hπ h

noncomputable def stageStop {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) : Environment d → ℕ :=
  hittingBtwn (stageTestMass e f a Gminus Gplus π H)
    (Set.Iio (ENNReal.ofReal (Real.exp (-B)))) 1 (min H R)

lemma stageStop_stopping {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) (H R : ℕ) :
    IsStoppingTime (rowHeightFiltration (realPosition (step e)) a)
      (fun ω => (stageStop e f a Gminus Gplus B π H R ω : WithTop ℕ)) :=
  (stageTestMass_adapted e f a Gminus Gplus π hπ H).isStoppingTime_hittingBtwn measurableSet_Iio

lemma before_stageStop_pass {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (ω : Environment d)
    {h : ℕ} (hh : 0<h) (hlt : h<stageStop e f a Gminus Gplus B π H R ω) :
    ENNReal.ofReal (Real.exp (-B))≤ stageEndpointMass e f a Gminus π h ω := by
  have hp := notMem_of_lt_hittingBtwn hlt hh
  change ¬ stageTestMass e f a Gminus Gplus π H h ω<ENNReal.ofReal (Real.exp (-B)) at hp
  have hp := le_of_not_gt hp
  simp only [stageTestMass,ite_eq_right (Nat.ne_of_gt hh)] at hp
  split at hp
  · exact hp.trans (min_le_left _ _)
  · exact hp

lemma stage_pass_retains {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H h : ℕ) (ω : Environment d)
    (hh : 0<h) (hp : ENNReal.ofReal (Real.exp (-B))≤ stageTestMass e f a Gminus Gplus π H h ω) :
    ENNReal.ofReal (Real.exp (-B))≤ stageEndpointMass e f a Gminus π h ω ∧
      (h=H → ENNReal.ofReal (Real.exp (-B))≤ stageEndpointMass e f a Gplus π h ω) := by
  simp only [stageTestMass,ite_eq_right (Nat.ne_of_gt hh)] at hp
  by_cases hH : h=H
  · simp only [ite_eq_left hH,le_min_iff] at hp
    exact ⟨hp.1,fun _ => hp.2⟩
  · simp only [ite_eq_right hH] at hp
    exact ⟨hp,fun he => (hH he).elim⟩

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace DirectionalTransience

lemma adapted_product_moment {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable[ℱ (n+1)] (X n))
    (c : ℝ≥0∞)
    (hstep : ∀ n (w : Ω → ℝ≥0∞), Measurable[ℱ n] w →
      (∫⁻ ω, w ω*X n ω ∂μ) ≤ c*(∫⁻ ω, w ω ∂μ)) :
    ∀ n, (∫⁻ ω, ∏ i∈Finset.range n, X i ω ∂μ) ≤ c^n := by
  have hm (n : ℕ) : Measurable[ℱ n] (fun ω => ∏ i∈Finset.range n, X i ω) := by
    apply Finset.measurable_fun_prod
    intro i hi
    exact (hX i).mono (ℱ.mono (by simpa using hi)) le_rfl
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [Finset.prod_range_succ]
    exact (hstep n _ (hm n)).trans (by simpa [pow_succ,mul_comm] using mul_le_mul_left ih c)

lemma adapted_exp_sum_tail {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable[ℱ (n+1)] (X n))
    (t C : ℝ) (ht : 0<t)
    (hstep : ∀ n (w : Ω → ℝ≥0∞), Measurable[ℱ n] w →
      (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp (t*X n ω)) ∂μ) ≤
        ENNReal.ofReal (Real.exp C)*(∫⁻ ω, w ω ∂μ)) (n : ℕ) (v : ℝ) :
    μ {ω | v ≤ ∑ i∈Finset.range n, X i ω} ≤
      ENNReal.ofReal (Real.exp (C*n-t*v)) := by
  let Y := fun i ω => ENNReal.ofReal (Real.exp (t*X i ω))
  have hY (i : ℕ) : Measurable[ℱ (i+1)] (Y i) := ((hX i).const_mul t).exp.ennreal_ofReal
  have hprod := adapted_product_moment μ ℱ Y hY (ENNReal.ofReal (Real.exp C)) hstep n
  have hsum : Measurable (fun ω => ∑ i∈Finset.range n, X i ω) :=
    Finset.measurable_fun_sum _ (fun i _ => (hX i).mono (ℱ.le _) le_rfl)
  have hid (ω : Ω) : (∏ i∈Finset.range n, Y i ω)=
      ENNReal.ofReal (Real.exp (t*∑ i∈Finset.range n, X i ω)) := by
    simp only [Y,← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos (t*X i ω)).le),
      ← Real.exp_sum,Finset.mul_sum]
  simp_rw [hid] at hprod
  have hmeas : Measurable (fun ω => ENNReal.ofReal (Real.exp (t*∑ i∈Finset.range n, X i ω))) :=
    (hsum.const_mul t).exp.ennreal_ofReal
  have he : {ω | v≤∑ i∈Finset.range n, X i ω} =
      {ω | ENNReal.ofReal (Real.exp (t*v))≤ENNReal.ofReal (Real.exp (t*∑ i∈Finset.range n, X i ω))} := by
    ext ω
    simp only [Set.mem_ofPred_eq,ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
      Real.exp_le_exp,mul_le_mul_iff_right₀ ht]
  rw [he]
  apply (meas_ge_le_lintegral_div hmeas.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top).trans
  calc
    _ ≤ ENNReal.ofReal (Real.exp C)^n/ENNReal.ofReal (Real.exp (t*v)) :=
      ENNReal.div_le_div_right hprod _
    _ = ENNReal.ofReal (Real.exp (C*n-t*v)) := by
      rw [← ENNReal.ofReal_pow (Real.exp_pos C).le,← ENNReal.ofReal_div_of_pos (Real.exp_pos _),
        ← Real.exp_nat_mul,← Real.exp_sub]
      congr 2
      ring

end DirectionalTransience

end

end OAI
