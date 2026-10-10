import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetLoss
import OAI.Probability.Ballisticity.Estimates.CappedLoss

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_relativeBudgetMass_fixed {d k : ℕ} (e f : Direction d)
    (base G : ℝ) (H : ℕ) (b : ℝ) (π : BudgetProfile (k:=k) e f base G) :
    Measurable (fun ω => relativeBudgetMass e f H b π.val ω) := by
  have hm : @Measurable _ _ (rowSigma Set.univ) _
      (fun ω => relativeBudgetMass e f H b π.val ω) :=
    (budgetProfileMass_joint_rows e f base G H b Set.univ
      (fun _ _ _ => Set.subset_univ _)).comp (measurable_const.prodMk measurable_id)
  exact hm.mono (rowSigma_le _) le_rfl

lemma relativeBudgetMass_bounds {d k : ℕ} (e f : Direction d) (H : ℕ) (b : ℝ)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    0≤relativeBudgetMass e f H b π ω ∧ relativeBudgetMass e f H b π ω≤1 := by
  rw [← relativeBudgetMassENN_toReal]
  exact ⟨ENNReal.toReal_nonneg,by
    have := ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞)≠∞) (relativeBudgetMassENN_le_one e f H b π ω)
    simpa using this⟩

lemma relativeBudgetMass_lt_exp {d k : ℕ} (e f : Direction d) (H : ℕ) (b x : ℝ)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    relativeBudgetMass e f H b π ω<Real.exp (-x) ↔
      relativeBudgetMassENN e f H b π ω<ENNReal.ofReal (Real.exp (-x)) := by
  rw [← relativeBudgetMassENN_toReal]
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos (-x)).le] using
    (ENNReal.toReal_lt_toReal (ne_top_of_le_ne_top (by norm_num)
      (relativeBudgetMassENN_le_one e f H b π ω))
      (ENNReal.ofReal_ne_top (r := Real.exp (-x))))

theorem actual_late_step_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) (θ : ℝ) (hθ : 0<θ) :
    ∃ lam Cmg : ℝ, 0<lam ∧ lam≤1 ∧ 0<Cmg ∧
      ∀ (k : ℕ), 2≤k → ∀ a : ℝ, 1≤a → ∀ D : ℕ → ℝ, (∀ L, 0≤D L) →
      ∃ l₀ : ℕ, ∀ Bstar : ℝ, 0<Bstar → ∃ Gzero : ℕ,
      ∀ l≥l₀, a*(l+1)≤Bstar → ∀ (H : ℕ) (base G b : ℝ),
        0<b → b≤G/2 → (Gzero:ℝ)≤G-b →
        (∀ L : ℕ, 1≤L → (H:ℝ)/fluctuationScale
          (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L)) ≤
            D L*Real.exp (-θ*l)) →
        ∀ π : BudgetProfile (k:=k) e f base G,
          (∫ ω, Real.exp ((lam/4)*cappedLogLoss (a*(l+1))
            (relativeBudgetMass e f H b π.val ω)) ∂environmentLaw ν) ≤Real.exp (Cmg*k) ∧
          (environmentLaw ν).real {ω | relativeBudgetMassENN e f H b π.val ω<
            ENNReal.ofReal (Real.exp (-(a*(l+1))))}≤Real.exp (-lam*(a*(l+1))/2) := by
  obtain ⟨κ,lam,C,hκ,hrows,hlam,hlam1,hC,hloss⟩ := rapid_loss_probability ν hue e f hef htrans
  have hκ0 : 0<(κ:ℝ) := hκ
  have hκ1 : (κ:ℝ)≤1 := by
    obtain ⟨p,hp⟩ := hrows.exists
    exact_mod_cast (hp e).trans (row_entry_le_one p e)
  let K := Real.log (1/(κ:ℝ))
  have hK : 0≤K := Real.log_nonneg ((one_le_div hκ0).mpr hκ1)
  obtain ⟨C₀,hC₀,harith⟩ := late_step_tail_arithmetic lam C θ K hlam hC.le hθ hK
  refine ⟨lam,C₀+1,hlam,hlam1,by positivity,?_⟩
  intro k hk a ha D hD
  have hk1 : 1≤k := by omega
  have hk1r : (1:ℝ)≤k := by exact_mod_cast hk1
  let D' := fun L => C*k*D L
  have hD' : ∀ L, 0≤D' L := fun L => mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg k)) (hD L)
  obtain ⟨l₀,hl₀⟩ := harith k hk1 a ha D' hD'
  refine ⟨l₀,fun Bstar hB => ?_⟩
  obtain ⟨Gzero,hGzero⟩ := hloss Bstar hB k hk1
  refine ⟨Gzero,?_⟩
  intro l hl hcap H base G b hb hhalf hG hratio π
  let T := fun x => (environmentLaw ν).real {ω | relativeBudgetMassENN e f H b π.val ω<ENNReal.ofReal (Real.exp (-x))}
  have hT : ∀ x, T x≤1 := fun x => by
    exact measureReal_le_one
  have htail (L : ℕ) (hL : 1≤L) (x : ℝ) (hx : (k:ℝ)*L*K≤x) (hxa : x≤a*(l+1)) :
      T x≤(Real.exp (C*k-lam*x/L)+D' L*Real.exp (x/L-θ*l))^L := by
    apply (hGzero L H base G b x hL hb hhalf hG hx (hxa.trans hcap) π).trans
    have hn := fluctuationScale_nonneg
      (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L))
    apply pow_le_pow_left₀ (by positivity)
    apply add_le_add_right
    calc
      C*k*Real.exp (x/L)*H/fluctuationScale
          (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L)) =
          (C*k*Real.exp (x/L))*((H:ℝ)/fluctuationScale
            (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L))) := by ring
      _ ≤ (C*k*Real.exp (x/L))*(D L*Real.exp (-θ*l)) :=
        mul_le_mul_of_nonneg_left (hratio L hL) (by positivity)
      _ = D' L*Real.exp (x/L-θ*l) := by dsimp [D']; rw [sub_eq_add_neg,Real.exp_add]; ring_nf
  obtain ⟨hsmall,hlarge⟩ := hl₀ l hl T hT htail
  refine ⟨?_,hlarge⟩
  let q := fun ω => relativeBudgetMass e f H b π.val ω
  let X := fun ω => cappedLogLoss (a*(l+1)) (q ω)
  have hq : Measurable q := measurable_relativeBudgetMass_fixed e f base G H b π
  have hqa : ∀ ω, 0≤q ω ∧ q ω≤1 := relativeBudgetMass_bounds e f H b π.val
  have hcap0 : 0≤a*(l+1) := mul_nonneg (by linarith only [ha]) (by positivity)
  have hX : Measurable X := measurable_cappedLogLoss _ q hq
  have hX0 : ∀ ω, 0≤X ω := fun ω => (cappedLogLoss_bounds hcap0 (hqa ω).1 (hqa ω).2).1
  have hXa : ∀ ω, X ω≤a*(l+1) := fun ω => (cappedLogLoss_bounds hcap0 (hqa ω).1 (hqa ω).2).2
  have hbound (x : ℝ) (hx : 0≤x) : environmentLaw ν {ω | x<X ω}≤
      ENNReal.ofReal (Real.exp (C₀*k)*Real.exp (-2*(lam/4)*x)) := by
    by_cases hxc : x<a*(l+1)
    · have he : {ω | x<X ω}={ω | relativeBudgetMassENN e f H b π.val ω<ENNReal.ofReal (Real.exp (-x))} := by
        ext ω
        change x<cappedLogLoss _ (q ω) ↔ _
        rw [lt_cappedLogLoss_iff (hqa ω).1 hx,and_iff_right hxc]
        exact relativeBudgetMass_lt_exp e f H b x π.val ω
      rw [he]
      apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
      apply (hsmall x hx hxc.le).trans
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      ring_nf
      exact le_rfl
    · have he : {ω | x<X ω}=∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun ω hω => (not_lt_of_ge ((hXa ω).trans (not_lt.mp hxc))) hω)
      rw [he,measure_empty]
      exact bot_le
  have hm := exp_moment_of_tail (environmentLaw ν) X hX hX0 (a*(l+1)) hXa
    (lam/4) (Real.exp (C₀*k)) (by positivity) (Real.exp_pos _).le hbound
  apply hm.trans
  calc
    1+Real.exp (C₀*k) ≤ 2*Real.exp (C₀*k) := by
      have hh := Real.one_le_exp_iff.mpr (mul_nonneg hC₀.le (Nat.cast_nonneg k))
      linarith only [hh]
    _ ≤ Real.exp ((C₀+1)*k) := by
      have he : (2:ℝ)≤Real.exp (k:ℝ) := by
        have hh := Real.add_one_le_exp (k:ℝ)
        linarith only [hh,hk1r]
      calc
        _ ≤ Real.exp (k:ℝ)*Real.exp (C₀*k) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring

end DirectionalTransience

end

end OAI
