import OAI.NumberTheory.DukePrimeDegree.Dynamics.SmallReturnRefinement
import OAI.NumberTheory.DukePrimeDegree.Entropy.LastActiveObservation
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace OAI

/-! # Entropy budgets for observations on sparse sections -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace DukePrimeDegree

private lemma summable_option_of_summable_some {α : Type*}
    (f : Option α → ℝ) (hf : Summable (fun a => f (some a))) : Summable f := by
  let e : Option α ≃ α ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit α
  have H : Summable (fun z : α ⊕ PUnit.{1} => f (e.symm z)) := by
    apply Summable.sum
    · simpa only [Function.comp_def,e,Equiv.optionEquivSumPUnit_symm_inl] using hf
    · exact (hasSum_fintype _).summable
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using H.comp_injective e.injective

/-- A row-wise budget controls both the rare-label mass and its entropy. -/
theorem sparse_distribution_information_le (K : ℕ → ℕ)
    (p : Option (Σ n : ℕ, Fin (K n)) → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1)
    (hs : Summable p) (hsum : ∑' z, p z=1)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hws : Summable w)
    (hsmall : ∀ n (i : Fin (K n)), p (some ⟨n,i⟩) ≤ w n/(K n+1:ℝ))
    (hinfo : ∀ n (i : Fin (K n)),
      Real.negMulLog (p (some ⟨n,i⟩)) ≤ w n/(K n+1:ℝ)) :
    Summable (fun z => Real.negMulLog (p z)) ∧
      (∑' z, Real.negMulLog (p z)) ≤ 2*∑' n, w n := by
  let f (z : Σ n : ℕ, Fin (K n)) := Real.negMulLog (p (some z))
  have hf0 (z) : 0 ≤ f z := Real.negMulLog_nonneg (hp _) (hp1 _)
  have hrow (n) : (∑' i : Fin (K n), f ⟨n,i⟩) ≤ w n := by
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _i : Fin (K n), w n/(K n+1:ℝ) :=
        Finset.sum_le_sum fun i _ => hinfo n i
      _ ≤ w n := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hden : (0:ℝ)<K n+1 := by positivity
        have he := div_mul_cancel₀ (w n) hden.ne'
        nlinarith [hw n]
  have hrows : Summable (fun n => ∑' i : Fin (K n), f ⟨n,i⟩) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => hf0 _) hrow hws
  have hf : Summable f := (summable_sigma_of_nonneg hf0).mpr
    ⟨fun _ => (hasSum_fintype _).summable,hrows⟩
  have hfle : (∑' z, f z) ≤ ∑' n, w n := by
    rw [hf.tsum_sigma]
    exact hrows.tsum_le_tsum hrow hws
  have hmassrows (n) : (∑' i : Fin (K n), p (some ⟨n,i⟩)) ≤ w n := by
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _i : Fin (K n), w n/(K n+1:ℝ) :=
        Finset.sum_le_sum fun i _ => hsmall n i
      _ ≤ w n := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hden : (0:ℝ)<K n+1 := by positivity
        have he := div_mul_cancel₀ (w n) hden.ne'
        nlinarith [hw n]
  have hps : Summable (fun z : Σ n : ℕ, Fin (K n) => p (some z)) :=
    hs.comp_injective (Option.some_injective _)
  have hmass : (∑' z : Σ n : ℕ, Fin (K n), p (some z)) ≤ ∑' n, w n := by
    rw [hps.tsum_sigma]
    exact hps.sigma.tsum_le_tsum hmassrows hws
  have hbase : Real.negMulLog (p none) ≤ ∑' n, w n := by
    have H := Real.negMulLog_le_one_sub_self (hp none)
    rw [tsum_option_eq p hs] at hsum
    linarith
  have hfull := summable_option_of_summable_some
    (fun z => Real.negMulLog (p z)) hf
  refine ⟨hfull,?_⟩
  rw [tsum_option_eq _ hfull]
  change Real.negMulLog (p none)+(∑' z, f z) ≤ _
  linarith

lemma exists_small_mass_information_budget {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ b ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ δ → Real.negMulLog p ≤ b := by
  have ht : Filter.Tendsto Real.negMulLog (nhds 0) (nhds 0) := by
    have H := Real.continuous_negMulLog.continuousAt (x := 0)
    change Filter.Tendsto Real.negMulLog (nhds 0) (nhds (Real.negMulLog 0)) at H
    simpa only [Real.negMulLog_zero] using H
  obtain ⟨r,hr,H⟩ := Metric.tendsto_nhds_nhds.mp ht b hb
  refine ⟨min b (r/2),lt_min hb (by positivity),min_le_left _ _,?_⟩
  intro p hp hpδ
  have hpr : dist p 0 < r := by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hp]
    have := hpδ.trans (min_le_right b (r/2))
    linarith
  have he := H hpr
  rw [Real.dist_eq,sub_zero] at he
  exact (le_abs_self _).trans he.le

/-- The finite label cardinalities may grow arbitrarily fast: their
section masses can be chosen afterwards to absorb their Shannon cost. -/
theorem exists_sparse_distribution_budget (K : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Summable δ ∧
      (∑' n, δ n) ≤ ε/4 ∧
      ∀ p : Option (Σ n : ℕ, Fin (K n)) → ℝ,
        (∀ z, 0 ≤ p z) → (∀ z, p z ≤ 1) → Summable p → (∑' z, p z)=1 →
        (∀ n (i : Fin (K n)), p (some ⟨n,i⟩) ≤ δ n) →
        Summable (fun z => Real.negMulLog (p z)) ∧
          (∑' z, Real.negMulLog (p z)) < ε := by
  let w : ℕ → ℝ := fun n => (ε/4)*(1/2:ℝ)^(n+1)
  have hw (n) : 0 < w n := by dsimp only [w]; positivity
  have hws : Summable w := by
    simpa only [w,pow_succ',←mul_assoc] using
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_left ((ε/4)*(1/2))
  have hwSum : (∑' n, w n)=ε/4 := by
    simp only [w,pow_succ',←mul_assoc,tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)]
    ring
  choose δ hδ hδb hδI using fun n => exists_small_mass_information_budget
    (b := w n/(K n+1:ℝ)) (div_pos (hw n) (by positivity))
  have hδw (n) : δ n ≤ w n := (hδb n).trans (by
    apply div_le_self (hw n).le
    linarith [Nat.cast_nonneg (α := ℝ) (K n)])
  have hδs := Summable.of_nonneg_of_le (fun n => (hδ n).le) hδw hws
  refine ⟨δ,hδ,hδs,(hδs.tsum_le_tsum hδw hws).trans_eq hwSum,?_⟩
  intro p hp hp1 hs hsum hsmall
  obtain ⟨hI,hIle⟩ := sparse_distribution_information_le K p hp hp1 hs hsum w
    (fun n => (hw n).le) hws
    (fun n i => (hsmall n i).trans (hδb n))
    (fun n i => hδI n _ (hp _) (hsmall n i))
  refine ⟨hI,?_⟩
  rw [hwSum] at hIle
  linarith

end DukePrimeDegree

end

end OAI
