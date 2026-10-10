import Mathlib
import OAI.Probability.Ballisticity.Coupling.FreshThreat
import OAI.Probability.Ballisticity.Estimates.BudgetAlgebra

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma budget_loss_requires_retries {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r s : ℝ) (hr : 0 ≤ r) (hs : s ≤ 1) (κ : ℝ≥0) (t : ℝ≥0∞)
    (ht : t ≤ 1) (hkt : t ≤ (κ:ℝ≥0∞)^k*ENNReal.ofReal s)
    (n H : ℕ) (a G : ℝ) (π : Environment d → BudgetProfile (k:=k) e f a G)
    (ω : Environment d) (hκ : ∀ y, κ ≤ (ω y).1 e)
    (hbad : relativeBudgetMassENN e f H ((n:ℝ)*r) (π ω).val ω < t^n) :
    ω ∈ budgetRetryEvent e f r s hr n H a G π := by
  induction n generalizing H a G with
  | zero => exact Set.mem_univ _
  | succ n ih =>
    have hpow : t^(n+1) ≤ 1 := pow_le_one₀ bot_le ht
    have hH : 1 ≤ H := by
      by_contra hn
      have h0 : H=0 := by omega
      rw [h0,relativeBudgetMassENN_zero e f _ (mul_nonneg (Nat.cast_nonneg _) hr)] at hbad
      exact (not_lt.mpr hpow) hbad
    let τ := budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω
    have htau : 1 ≤ τ := le_hittingBtwn hH ω
    have htaum : τ ≤ H := hittingBtwn_le ω
    have hmass : t ≤ relativeBudgetMassENN e f τ r (π ω).val ω :=
      hkt.trans (budgetFirstThreat_mass_lower e f hef a G r s hr hs π H hH ω κ hκ)
    have hbudget : r ≤ (n+1:ℕ)*r := by
      have hn : 0 ≤ (n:ℝ)*r := mul_nonneg (Nat.cast_nonneg n) hr
      push_cast; linarith
    have hthreat : τ < H := by
      by_contra hn
      have he : τ=H := by omega
      have hp : t^(n+1) ≤ t := by
        rw [pow_succ]
        calc
          _ ≤ 1*t := mul_le_mul_left (pow_le_one₀ bot_le ht) t
          _ = t := one_mul t
      exact (not_lt.mpr ((hp.trans (by simpa only [he] using hmass)).trans
        (relativeBudgetMassENN_mono e f H hbudget (π ω).val ω))) hbad
    let π' := fun η => nextBudgetProfile e f τ a G r hr (π η) η
    have hbad' : relativeBudgetMassENN e f (H-τ) ((n:ℝ)*r) (π' ω).val ω < t^n := by
      by_contra hn
      have hp := relativeBudgetMassENN_restart_comp e f τ (H-τ) a G r ((n:ℝ)*r) hr
        (mul_nonneg (Nat.cast_nonneg n) hr) (π ω) ω
      rw [Nat.add_sub_of_le htaum,
        show r+(n:ℝ)*r = ((n+1:ℕ):ℝ)*r by push_cast; ring] at hp
      have hb : t^(n+1) ≤ relativeBudgetMassENN e f H ((n+1:ℕ)*r) (π ω).val ω := by
        rw [pow_succ,mul_comm]
        exact (mul_le_mul hmass (le_of_not_gt hn) bot_le bot_le).trans hp
      exact (not_lt.mpr hb) hbad
    have hi := ih (H-τ) (a+τ) (G-r) π' hbad'
    apply Set.mem_iUnion.mpr
    exact ⟨⟨τ,by omega,hthreat⟩,rfl,hi⟩

theorem budget_rapid_loss_from_fresh_bound {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) (r s g : ℝ) (hr : 0 ≤ r) (hs : s ≤ 1)
    (κ : ℝ≥0) (hκ : ∀ᵐ ω ∂environmentLaw ν, ∀ y, κ ≤ (ω y).1 e)
    (t : ℝ≥0∞) (ht : t ≤ 1) (hkt : t ≤ (κ:ℝ≥0∞)^k*ENNReal.ofReal s)
    (n H : ℕ) (c : ℝ≥0∞)
    (hb : ∀ (h : ℕ), h ≤ H → ∀ (a G : ℝ), g ≤ G →
      ∀ π : BudgetProfile (k:=k) e f a G,
        environmentLaw ν (budgetThreatEvent e f h r π.val s) ≤ c)
    (a G : ℝ) (hG : g+n*r ≤ G) (π : BudgetProfile (k:=k) e f a G) :
    environmentLaw ν {ω | relativeBudgetMassENN e f H ((n:ℝ)*r) π.val ω < t^n} ≤ c^n := by
  have hsub : {ω | relativeBudgetMassENN e f H ((n:ℝ)*r) π.val ω < t^n} ≤ᵐ[environmentLaw ν]
      budgetRetryEvent e f r s hr n H a G (fun _ => π) := by
    filter_upwards [hκ] with ω hω hbad
    exact budget_loss_requires_retries e f hef r s hr hs κ t ht hkt n H a G (fun _ => π) ω hω hbad
  apply (measure_mono_ae hsub).trans
  simpa using budgetRetryEvent_probability ν e f r s g hr H c hb n H le_rfl a G hG
    (fun _ => π) measurable_const Set.univ MeasurableSet.univ

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem rapid_loss_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ (κ : ℝ≥0) (lam C : ℝ), 0 < κ ∧ (∀ᵐ p ∂ν, ∀ u, κ ≤ p.1 u) ∧
      0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ Gzero : ℕ,
      ∀ (L H : ℕ) (a G b x : ℝ), 1 ≤ L → 0 < b → b ≤ G/2 →
        (Gzero:ℝ) ≤ G-b → (k:ℝ)*L*Real.log (1/(κ:ℝ)) ≤ x → x ≤ Bstar →
        ∀ π : BudgetProfile (k:=k) e f a G,
          (environmentLaw ν).real {ω | relativeBudgetMassENN e f H b π.val ω <
            ENNReal.ofReal (Real.exp (-x))} ≤
          (Real.exp (C*k-lam*x/L) + C*k*Real.exp (x/L)*H /
            fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
              (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L)))^L := by
  obtain ⟨κ,hκ,hrows⟩ := hue
  have hue : UniformElliptic ν := ⟨κ,hκ,hrows⟩
  have hκ0 : 0 < (κ:ℝ) := hκ
  have hκ1 : (κ:ℝ) ≤ 1 := by
    obtain ⟨p,hp⟩ := hrows.exists
    exact_mod_cast (hp e).trans (row_entry_le_one p e)
  have henv : ∀ᵐ ω ∂environmentLaw ν, ∀ y, κ ≤ (ω y).1 e := by
    apply ae_all_iff.mpr
    intro y
    exact ((measurePreserving_eval_infinitePi (fun _ : Lattice d => ν) y).quasiMeasurePreserving.ae hrows).mono
      fun p hp => hp e
  obtain ⟨lam,C,D,hlam,hlam1,hC,hD,hfresh⟩ := fresh_budget_threat_bound ν hue e f htrans
  let K := Real.log (1/(κ:ℝ))
  have hK : 0 ≤ K := by
    dsimp [K]
    apply Real.log_nonneg
    exact (one_le_div hκ0).mpr hκ1
  have hlog : Real.log (κ:ℝ) = -K := by simp [K]
  let C' := max (C+lam*K) D
  have hC' : 0 < C' := hD.trans_le (le_max_right _ _)
  refine ⟨κ,lam,C',hκ,hrows,hlam,hlam1,hC',?_⟩
  intro Bstar hB k hk
  obtain ⟨Gzero,hGzero⟩ := hfresh Bstar hB k hk
  refine ⟨Gzero,?_⟩
  intro L H a G b x hL hb hhalf hG hx hxb π
  have hL0 : 0 < (L:ℝ) := by exact_mod_cast (by omega : 0<L)
  have hLn : (L:ℝ) ≠ 0 := ne_of_gt hL0
  have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  have hx0 : 0 ≤ x := (mul_nonneg (mul_nonneg hk0 hL0.le) hK).trans hx
  have hxl : (k:ℝ)*K ≤ x/L := (le_div_iff₀ hL0).mpr (by nlinarith [hx])
  have hxlB : x/L ≤ Bstar := by
    have hL1 : 1 ≤ (L:ℝ) := by exact_mod_cast hL
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  let s := Real.exp ((k:ℝ)*K-x/L)
  have hs0 : 0 < s := Real.exp_pos _
  have hs1 : s ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsB : Real.exp (-Bstar) ≤ s := Real.exp_le_exp.mpr (by
    have : 0 ≤ (k:ℝ)*K := mul_nonneg hk0 hK
    linarith)
  let t := ENNReal.ofReal (Real.exp (-x/L))
  have ht : t ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx0) hL0.le
  have hkt : t = (κ:ℝ≥0∞)^k*ENNReal.ofReal s := by
    have he : (κ:ℝ)^k*s = Real.exp (-x/L) := by
      have hpow : (κ:ℝ)^k = Real.exp ((k:ℝ)*Real.log (κ:ℝ)) := by
        rw [Real.exp_nat_mul,Real.exp_log hκ0]
      rw [hpow,hlog,← Real.exp_add]
      congr 1
      ring
    rw [← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_pow hκ0.le,
      ← ENNReal.ofReal_mul (pow_nonneg hκ0.le k),he]
  let N := fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L))
  have hN : 0 ≤ N := fluctuationScale_nonneg _ _ _
  let c := Real.exp (C'*k-lam*x/L)+C'*k*Real.exp (x/L)*H/N
  have hc : 0 ≤ c := add_nonneg (Real.exp_pos _).le (by positivity)
  have hbound (h : ℕ) (hh : h ≤ H) (a' G' : ℝ) (hG' : (Gzero:ℝ) ≤ G')
      (π' : BudgetProfile (k:=k) e f a' G') :
      environmentLaw ν (budgetThreatEvent e f h (b/L) π'.val s) ≤ ENNReal.ofReal c := by
    have hsep : ∀ᵐ u ∂π'.val, Pairwise fun i j => (Gzero:ℤ) ≤ |u i f.1-u j f.1| := by
      filter_upwards [π'.property.2] with u hu
      apply (tupleSeparated_coordinate f Gzero u).mp
      exact tupleSeparated_mono f hG' u hu.2
    have hb0 : 0 < b/(2*L) := div_pos hb (mul_pos (by norm_num) hL0)
    have hf := hGzero π'.val hsep h (b/(2*L)) s hb0 hsB
    have hrad : 2*(b/(2*L)) = b/L := by field_simp
    rw [hrad] at hf
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc).mpr
    apply hf.trans
    apply add_le_add
    · calc
        Real.exp (C*k)*s^lam = Real.exp ((C+lam*K)*k-lam*x/L) := by
          rw [Real.rpow_def_of_pos hs0]
          dsimp only [s]
          rw [Real.log_exp,← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (C'*k-lam*x/L) := Real.exp_le_exp.mpr (by
          have : (C+lam*K)*k ≤ C'*k := mul_le_mul_of_nonneg_right (le_max_left _ _) hk0
          linarith)
    · have hinv : 1/s ≤ Real.exp (x/L) := by
        dsimp only [s]
        rw [one_div,← Real.exp_neg]
        apply Real.exp_le_exp.mpr
        have : 0 ≤ (k:ℝ)*K := mul_nonneg hk0 hK
        linarith
      have hD' : D*k*(h:ℝ)/N ≤ C'*k*(H:ℝ)/N := by
        apply div_le_div_of_nonneg_right _ hN
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hk0
        · exact_mod_cast hh
        · exact Nat.cast_nonneg h
        · exact mul_nonneg hC'.le hk0
      calc
        D*k*h/N/s = (D*k*h/N)*(1/s) := by ring
        _ ≤ (C'*k*H/N)*Real.exp (x/L) := mul_le_mul hD' hinv
          (one_div_nonneg.mpr hs0.le) (by positivity)
        _ = C'*k*Real.exp (x/L)*H/N := by ring
  have hbudget : (L:ℝ)*(b/L) = b := mul_div_cancel₀ _ hLn
  have hsep : (Gzero:ℝ)+(L:ℝ)*(b/L) ≤ G := by rw [hbudget]; linarith
  have hloss := budget_rapid_loss_from_fresh_bound ν e f hef (b/L) s Gzero
    (div_nonneg hb.le hL0.le) hs1 κ henv t ht hkt.le L H (ENNReal.ofReal c)
    hbound a G hsep π
  have htL : t^L = ENNReal.ofReal (Real.exp (-x)) := by
    dsimp only [t]
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,← Real.exp_nat_mul]
    congr 2
    field_simp
  rw [hbudget,htL,← ENNReal.ofReal_pow hc] at hloss
  exact ENNReal.toReal_le_of_le_ofReal (pow_nonneg hc L) hloss

end DirectionalTransience

end

end OAI
