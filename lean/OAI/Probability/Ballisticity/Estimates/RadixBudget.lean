import Mathlib
import OAI.Probability.Ballisticity.Estimates.ProtectionLoss

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma radix16_budget_ratio {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0<μ {x | S x≠0}) {ρ c C : ℝ} (hρ : 0<ρ) (hc : 0<c) (hc1 : c≤1)
    (hC : 0≤C) (l L H : ℕ) (hL : 1≤L)
    (hH : (H:ℝ)≤3*C*fluctuationScale μ S ρ/(16:ℝ)^l) :
    (H:ℝ)/fluctuationScale μ S (((c/16)*ρ/(2:ℝ)^l)/(2*L)) ≤
      (3*C*(32*(L:ℝ)/c)^2)*Real.exp (-(Real.log 4)*l) := by
  have hL0 : (0:ℝ)<L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hL1 : (1:ℝ)≤L := by exact_mod_cast hL
  have h2 : (0:ℝ)<(2:ℝ)^l := by positivity
  have h16 : (0:ℝ)<(16:ℝ)^l := by positivity
  let r := c/(32*(L:ℝ)*(2:ℝ)^l)
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r≤1 := by
    dsimp [r]
    apply (div_le_one (by positivity)).mpr
    have hp : (1:ℝ)≤(2:ℝ)^l := one_le_pow₀ (by norm_num)
    have hprod : 1≤(L:ℝ)*(2:ℝ)^l := one_le_mul_of_one_le_of_one_le hL1 hp
    nlinarith only [hc1,hprod]
  have hn : 0<fluctuationScale μ S ρ := by
    exact div_pos (sq_pos_of_pos hρ) (truncatedVariance_pos μ S hS hne hρ)
  have hn' : 0<fluctuationScale μ S (r*ρ) := by
    exact div_pos (sq_pos_of_pos (mul_pos hr hρ))
      (truncatedVariance_pos μ S hS hne (mul_pos hr hρ))
  have hscale := fluctuationScale_scaling μ S hS hne hρ hr hr1
  have heq : ((c/16)*ρ/(2:ℝ)^l)/(2*L)=r*ρ := by dsimp [r]; field_simp; ring
  rw [heq]
  calc
    (H:ℝ)/fluctuationScale μ S (r*ρ) ≤
        (3*C*fluctuationScale μ S ρ/(16:ℝ)^l)/(r^2*fluctuationScale μ S ρ) :=
      div_le_div₀ (by positivity) hH (by positivity) hscale
    _ = (3*C*(32*(L:ℝ)/c)^2) / (4:ℝ)^l := by
      have hp : ((2:ℝ)^l)^2*(4:ℝ)^l=(16:ℝ)^l := by
        rw [← pow_mul, mul_comm l 2, pow_mul, ← mul_pow]; norm_num
      dsimp [r]
      field_simp
      nlinarith only [congrArg (fun x : ℝ => C*x) hp]
    _ = _ := by
      rw [neg_mul,Real.exp_neg,mul_comm (Real.log 4) (l:ℝ),Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<4)]
      ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma adapted_weighted_product_moment {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable[ℱ (n+1)] (X n))
    (W : Ω → ℝ≥0∞) (hW : Measurable[ℱ 0] W) (c : ℝ≥0∞) (N : ℕ)
    (hstep : ∀ n<N, ∀ w : Ω → ℝ≥0∞, Measurable[ℱ n] w →
      (∫⁻ ω, w ω*X n ω ∂μ)≤c*(∫⁻ ω, w ω ∂μ)) :
    (∫⁻ ω, W ω*∏ i∈Finset.range N, X i ω ∂μ)≤c^N*(∫⁻ ω, W ω ∂μ) := by
  have hm (n : ℕ) : Measurable[ℱ n] (fun ω => W ω*∏ i∈Finset.range n, X i ω) := by
    apply (hW.mono (ℱ.mono (Nat.zero_le n)) le_rfl).mul
    apply Finset.measurable_fun_prod
    intro i hi
    exact (hX i).mono (ℱ.mono (by simpa using hi)) le_rfl
  induction N with
  | zero => simp
  | succ N ih =>
    simp_rw [Finset.prod_range_succ,← mul_assoc]
    apply (hstep N (Nat.lt_succ_self N) _ (hm N)).trans
    have hh := mul_le_mul_left (ih (fun n hn => hstep n (Nat.lt_trans hn (Nat.lt_succ_self N)))) c
    simpa [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh

lemma adapted_weighted_exp_sum_tail {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable[ℱ (n+1)] (X n))
    (W : Ω → ℝ≥0∞) (hW : Measurable[ℱ 0] W)
    (t C : ℝ) (ht : 0<t) (N : ℕ)
    (hstep : ∀ n<N, ∀ w : Ω → ℝ≥0∞, Measurable[ℱ n] w →
      (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp (t*X n ω)) ∂μ)≤
        ENNReal.ofReal (Real.exp C)*(∫⁻ ω, w ω ∂μ)) (v : ℝ) :
    μ.withDensity W {ω | v≤∑ i∈Finset.range N, X i ω}≤
      ENNReal.ofReal (Real.exp (C*N-t*v))*(∫⁻ ω, W ω ∂μ) := by
  let Y := fun i ω => ENNReal.ofReal (Real.exp (t*X i ω))
  have hY (i : ℕ) : Measurable[ℱ (i+1)] (Y i) := ((hX i).const_mul t).exp.ennreal_ofReal
  have hprod := adapted_weighted_product_moment μ ℱ Y hY W hW (ENNReal.ofReal (Real.exp C)) N hstep
  have hsum : Measurable (fun ω => ∑ i∈Finset.range N, X i ω) :=
    Finset.measurable_fun_sum _ (fun i _ => (hX i).mono (ℱ.le _) le_rfl)
  have hid (ω : Ω) : (∏ i∈Finset.range N, Y i ω)=
      ENNReal.ofReal (Real.exp (t*∑ i∈Finset.range N, X i ω)) := by
    simp only [Y,← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos (t*X i ω)).le),
      ← Real.exp_sum,Finset.mul_sum]
  simp_rw [hid] at hprod
  have hmeas : Measurable (fun ω => ENNReal.ofReal (Real.exp (t*∑ i∈Finset.range N, X i ω))) :=
    (hsum.const_mul t).exp.ennreal_ofReal
  have he : {ω | v≤∑ i∈Finset.range N, X i ω} =
      {ω | ENNReal.ofReal (Real.exp (t*v))≤ENNReal.ofReal (Real.exp (t*∑ i∈Finset.range N, X i ω))} := by
    ext ω
    simp only [Set.mem_ofPred_eq,ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
      Real.exp_le_exp,mul_le_mul_iff_right₀ ht]
  rw [he]
  apply (meas_ge_le_lintegral_div (μ:=μ.withDensity W) hmeas.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top).trans
  rw [lintegral_withDensity_eq_lintegral_mul μ (hW.mono (ℱ.le 0) le_rfl) hmeas]
  calc
    _ ≤ (ENNReal.ofReal (Real.exp C)^N*(∫⁻ ω, W ω ∂μ))/ENNReal.ofReal (Real.exp (t*v)) :=
      ENNReal.div_le_div_right hprod _
    _ = ENNReal.ofReal (Real.exp (C*N-t*v))*(∫⁻ ω, W ω ∂μ) := by
      rw [ENNReal.mul_div_right_comm,← ENNReal.ofReal_pow (Real.exp_pos C).le,
        ← ENNReal.ofReal_div_of_pos (Real.exp_pos _),← Real.exp_nat_mul,← Real.exp_sub]
      congr 2
      ring_nf

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def lateBudget (c ρ : ℝ) (s n : ℕ) : ℝ := (c/16)*ρ/(2:ℝ)^(s+n)

lemma lateBudget_pos {c ρ : ℝ} (hc : 0<c) (hρ : 0<ρ) (s n : ℕ) : 0<lateBudget c ρ s n := by
  unfold lateBudget; positivity

lemma lateBudget_sum_le {c ρ : ℝ} (hc : 0≤c) (hρ : 0≤ρ) (s n : ℕ) :
    (∑ i∈Finset.range n, lateBudget c ρ s i)≤c*ρ/8 := by
  have hgeom := geom_sum_mul_neg (1/2:ℝ) n
  have hnonneg : 0≤(1/2:ℝ)^n := by positivity
  have hsum : (∑ i∈Finset.range n, (1/2:ℝ)^i)≤2 := by linarith
  calc
    _ ≤ ∑ i∈Finset.range n, (c*ρ/16)*(1/2:ℝ)^i := by
      apply Finset.sum_le_sum; intro i hi
      unfold lateBudget
      have hpow : (2:ℝ)^i≤(2:ℝ)^(s+i) := pow_le_pow_right₀ (by norm_num) (Nat.le_add_left i s)
      calc
        _ ≤ (c/16)*ρ/(2:ℝ)^i := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
        _ = _ := by rw [one_div_pow]; ring
    _ = (c*ρ/16)*(∑ i∈Finset.range n, (1/2:ℝ)^i) := by rw [Finset.mul_sum]
    _ ≤ (c*ρ/16)*2 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

lemma lateBudget_gaps {c ρ : ℝ} (hc : 0<c) (hρ : 0<ρ) (s n : ℕ) :
    lateBudget c ρ s n≤protectionGap (3*c*ρ/4) (lateBudget c ρ s) n/2 ∧
    c*ρ/2≤protectionGap (3*c*ρ/4) (lateBudget c ρ s) n-lateBudget c ρ s n := by
  have hn := lateBudget_sum_le hc.le hρ.le s n
  have hn1 := lateBudget_sum_le hc.le hρ.le s (n+1)
  rw [Finset.sum_range_succ] at hn1
  have hb : lateBudget c ρ s n≤c*ρ/16 := by
    unfold lateBudget
    have ht : (1:ℝ)≤(2:ℝ)^(s+n) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ (c/16)*ρ/1 := div_le_div_of_nonneg_left (by positivity) (by norm_num) ht
      _ = _ := by ring
  rw [protectionGap_eq]
  constructor <;> nlinarith [mul_pos hc hρ]

lemma fixed_budget_momentENN {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (base G : ℝ) (H : ℕ) (b a t C : ℝ)
    (ha : 0≤a) (ht : 0≤t) (π : BudgetProfile (k:=k) e f base G)
    (hb : (∫ ω, Real.exp (t*cappedLogLoss a (relativeBudgetMass e f H b π.val ω))
      ∂environmentLaw ν)≤Real.exp C) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (t*cappedLogLoss a (relativeBudgetMass e f H b π.val ω)))
      ∂environmentLaw ν)≤ENNReal.ofReal (Real.exp C) := by
  have hi := integrable_exp_cappedLogLoss (environmentLaw ν) a t ha ht _
    (measurable_relativeBudgetMass_fixed e f base G H b π)
    (fun ω => (relativeBudgetMass_bounds e f H b π.val ω).1)
    (fun ω => (relativeBudgetMass_bounds e f H b π.val ω).2)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal hb

theorem scheduled_late_step_bounds {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ lam Cmg : ℝ, 0<lam ∧ lam≤1 ∧ 0<Cmg ∧
      ∀ (k : ℕ), 2≤k → ∀ a : ℝ, 1≤a → ∀ c C : ℝ, 0<c → c≤1 → 0<C →
      ∃ l₀ : ℕ, 0<l₀ ∧ ∀ Bstar : ℝ, 0<Bstar → ∃ R : ℝ, 0<R ∧
      ∀ ρ≥R, ∀ n : ℕ, a*(l₀+n+1)≤Bstar → ∀ H : ℕ,
        (H:ℝ)≤3*C*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) ρ/(16:ℝ)^(l₀+n) →
        ∀ base : ℝ, ∀ π : BudgetProfile (k:=k) e f base
          (protectionGap (3*c*ρ/4) (lateBudget c ρ l₀) n),
          (∫⁻ ω, ENNReal.ofReal (Real.exp ((lam/4)*cappedLogLoss (a*(l₀+n+1))
            (relativeBudgetMass e f H (lateBudget c ρ l₀ n) π.val ω))) ∂environmentLaw ν)≤
              ENNReal.ofReal (Real.exp (Cmg*k)) ∧
          environmentLaw ν {ω | relativeBudgetMass e f H (lateBudget c ρ l₀ n) π.val ω<
            Real.exp (-(a*(l₀+n+1)))}≤ENNReal.ofReal (Real.exp (-lam*(a*(l₀+n+1))/2)) := by
  obtain ⟨lam,Cmg,hlam,hlam1,hCmg,hh⟩ := actual_late_step_moment ν hue e f hef htrans (Real.log 4)
    (Real.log_pos (by norm_num))
  refine ⟨lam,Cmg,hlam,hlam1,hCmg,?_⟩
  intro k hk a ha c C hc hc1 hC
  let D := fun L : ℕ => 3*C*(32*(L:ℝ)/c)^2
  obtain ⟨lmin,hl₀⟩ := hh k hk a ha D (fun L => by dsimp [D]; positivity)
  let l₀ := lmin+1
  refine ⟨l₀,by dsimp [l₀]; omega,fun Bstar hB => ?_⟩
  obtain ⟨Gzero,hGzero⟩ := hl₀ Bstar hB
  refine ⟨max 1 (2*Gzero/c),lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro ρ hρR n hn H hH base π
  have hρ : 0<ρ := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hρR)
  have hG : (Gzero:ℝ)≤c*ρ/2 := by
    have hh := (le_max_right 1 (2*Gzero/c)).trans hρR
    have hh' := (div_le_iff₀ hc).mp hh
    nlinarith only [hh']
  let μ := independentConditionedPairLaw ν (realPosition (step e))
  let S := commonIncrementProcess (realPosition (step e)) f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν _
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
  have hS : Measurable S := measurable_commonIncrementProcess _ _ _
  have hne : 0<μ {x | S x≠0} := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hgaps := lateBudget_gaps hc hρ l₀ n
  have hcap : a*((l₀+n:ℕ)+1)≤Bstar := by exact_mod_cast hn
  have hb := hGzero (l₀+n) (by dsimp [l₀]; omega) hcap H base _ _
    (lateBudget_pos hc hρ l₀ n) hgaps.1 (hG.trans hgaps.2)
    (fun L hL => radix16_budget_ratio μ S hS hne hρ hc hc1 hC.le (l₀+n) L H hL hH) π
  constructor
  · apply fixed_budget_momentENN ν e f base _ H _ _ _ _ (by positivity) (by positivity) π
    simpa only [Nat.cast_add,Nat.cast_one] using hb.1
  · have he : {ω | relativeBudgetMass e f H (lateBudget c ρ l₀ n) π.val ω<Real.exp (-(a*(l₀+n+1)))}=
        {ω | relativeBudgetMassENN e f H (lateBudget c ρ l₀ n) π.val ω<ENNReal.ofReal (Real.exp (-(a*(l₀+n+1))))} := by
      ext ω; exact relativeBudgetMass_lt_exp e f H _ _ π.val ω
    rw [he]
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr
    simpa only [Nat.cast_add,Nat.cast_one,Measure.real] using hb.2

end DirectionalTransience

end

end OAI
