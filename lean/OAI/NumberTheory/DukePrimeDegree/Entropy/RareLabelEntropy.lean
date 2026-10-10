import OAI.NumberTheory.PrimePackets.RootSubgroups
import OAI.NumberTheory.PrimePackets.ConditionalOrbitEntropy

namespace OAI

/-! # The entropy cost of rare observation errors

This finite-label estimate converts small boundary-visit frequencies
into a small entropy cost for the neutral orbit covers.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def rareLabelCost (q : ℕ) (δ ε : ℝ) : ℝ :=
  -Real.log (1-δ) + ε * (Real.log q - Real.log δ)

theorem rareLabelCost_small (q : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ ε : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ε ∧
      ∀ p : ℝ, 0 ≤ p → p < ε → rareLabelCost q δ p < η := by
  let δ := 1-Real.exp (-η/2)
  have hd : 0 < δ := by
    have he : Real.exp (-η/2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    dsimp [δ]
    linarith
  have hd1 : δ < 1 := by dsimp [δ]; linarith [Real.exp_pos (-η/2)]
  let L := Real.log q-Real.log δ
  let ε := η/(2*(1+|L|))
  have he : 0 < ε := div_pos hη (by positivity)
  refine ⟨δ,ε,hd,hd1,he,?_⟩
  intro p hp hpε
  have hbase : -Real.log (1-δ) = η/2 := by
    dsimp [δ]
    rw [sub_sub_cancel,Real.log_exp]
    ring
  have hprod : p*(1+|L|) < η/2 := by
    have h := (mul_lt_mul_iff_left₀ (show 0 < 1+|L| by positivity)).mpr hpε
    have hden : 1+|L| ≠ 0 := ne_of_gt (by positivity)
    have hε : ε*(1+|L|)=η/2 := by dsimp [ε]; field_simp [hden]
    nlinarith
  have hL : p*L ≤ p*|L| := mul_le_mul_of_nonneg_left (le_abs_self L) hp
  change -Real.log (1-δ)+p*L < η
  rw [hbase]
  linarith

theorem finiteShannon_option_le {α : Type*} [Fintype α] [Nonempty α]
    (p : Option α → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    finiteShannon p ≤ rareLabelCost (Fintype.card α) δ (1-p none) := by
  let n : ℝ := Fintype.card α
  have hn : 0 < n := by
    change 0 < (Fintype.card α : ℝ)
    exact_mod_cast (Fintype.card_pos (α := α))
  let q : Option α → ℝ := fun a => match a with
    | none => 1-δ
    | some _ => δ/n
  have hq a : 0 < q a := by cases a <;> dsimp [q] <;> positivity
  have hqs : ∑ a, q a = 1 := by
    rw [Fintype.sum_option]
    simp only [q,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change 1-δ+n*(δ/n)=1
    field_simp [ne_of_gt hn]
    ring
  have H := finiteShannon_le_cross hp (fun a => (hq a).le) hs hqs
    (fun a ha => (ne_of_gt (hq a) ha).elim)
  have hsum : ∑ a : α, p (some a) = 1-p none := by
    rw [Fintype.sum_option] at hs
    linarith
  have hp1 : p none ≤ 1 := by
    have hnn : 0 ≤ ∑ a : α, p (some a) := Finset.sum_nonneg fun a _ => hp _
    linarith
  have hlog : Real.log (1-δ) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  have he : (∑ a : Option α, -p a * Real.log (q a)) =
      -p none * Real.log (1-δ) + (1-p none)*(Real.log n-Real.log δ) := by
    rw [Fintype.sum_option]
    simp only [q,Real.log_div (ne_of_gt hδ) (ne_of_gt hn)]
    have hh : (∑ a : α, -p (some a)*(Real.log δ-Real.log n)) =
        (∑ a : α, p (some a))*(Real.log n-Real.log δ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hh,hsum]
  rw [he] at H
  unfold rareLabelCost
  dsimp only [n] at H
  nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (neg_nonneg.mpr hlog)]

theorem observationEntropy_option_le {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] (μ : Measure Y) [IsProbabilityMeasure μ]
    (E : Y → Option α) (hE : ∀ a, MeasurableSet {y | E y=a})
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    observationEntropy μ E ≤
      rareLabelCost (Fintype.card α) δ (1-μ.real {y | E y=none}) :=
  finiteShannon_option_le (fun a => μ.real {y | E y=a})
    (fun _ => measureReal_nonneg)
    (observation_distribution_sum μ E hE) hδ hδ1

def observationError {Y α : Type*} [DecidableEq α] (P R : Y → α) (y : Y) : Option α :=
  if P y = R y then none else some (P y)

theorem conditionalObservationEntropy_le_error {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P R : Y → α) (hP : Measurable P) (hR : Measurable R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    conditionalObservationEntropy μ P R ≤
      rareLabelCost (Fintype.card α) δ (μ.real {y | P y ≠ R y}) := by
  let E := observationError P R
  have hE (a : Option α) : MeasurableSet {y | E y=a} := by
    cases a with
    | none =>
      convert (measurableSet_eq_fun hP hR) using 1
      ext y
      simp [E,observationError]
    | some a =>
      convert (measurableSet_eq_fun hP hR).compl.inter
        (hP (measurableSet_singleton a)) using 1
      ext y
      by_cases h : P y=R y <;> simp [E,observationError,h]
  have href : ∀ x y, (R x,E x) = (R y,E y) → (R x,P x) = (R y,P y) := by
    intro x y h
    have hr : R x=R y := congrArg Prod.fst h
    have he : E x=E y := congrArg Prod.snd h
    apply Prod.ext hr
    by_cases hx : P x = R x
    · have hy : P y = R y := by
        by_contra hy
        simp [E,observationError,hx,hy] at he
      exact hx.trans (hr.trans hy.symm)
    · by_cases hy : P y = R y
      · simp [E,observationError,hx,hy] at he
      · simpa only [E,observationError,ite_eq_right hx,ite_eq_right hy,Option.some.injEq] using he
  have H := observationEntropy_le_of_refines μ (fun y => (R y,P y))
    (fun y => (R y,E y))
    (observationPair_measurable_fiber R P
      (fun a => hR (measurableSet_singleton a)) (fun a => hP (measurableSet_singleton a)))
    (observationPair_measurable_fiber R E
      (fun a => hR (measurableSet_singleton a)) hE) href
  have H' := observationEntropy_joint_le μ R E
    (fun a => hR (measurableSet_singleton a))
    hE
  have herr := observationEntropy_option_le μ E hE hδ hδ1
  have heq : 1-μ.real {y | E y=none} = μ.real {y | P y ≠ R y} := by
    have hs : {y | E y=none} = {y | P y=R y} := by
      ext y
      simp [E,observationError]
    rw [hs,show {y | P y ≠ R y} = {y | P y=R y}ᶜ from rfl,
      measureReal_compl (measurableSet_eq_fun hP hR),probReal_univ]
  rw [heq] at herr
  unfold conditionalObservationEntropy
  linarith

end DukePrimeDegree

end

end OAI
