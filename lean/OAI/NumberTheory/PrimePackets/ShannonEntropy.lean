import Mathlib

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
namespace PrimeDegreePackets

 
def finiteShannon {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

lemma finiteShannon_nonneg {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (h1 : ∑ a, p a = 1) : 0 ≤ finiteShannon p := by
  classical
  apply Finset.sum_nonneg
  intro a _
  apply Real.negMulLog_nonneg (hp a)
  rw [← h1]
  exact Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)

lemma negMulLog_le_cross {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hzero : q = 0 → p = 0) :
    Real.negMulLog p ≤ -p * Real.log q + q-p := by
  by_cases hp0 : p = 0
  · simp [hp0,hq]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' : 0 < q := lt_of_le_of_ne hq (fun h => hp0 (hzero h.symm))
  have H := mul_le_mul_of_nonneg_right
    (Real.self_sub_one_le_mul_log (div_nonneg hp hq)) hq
  rw [Real.log_div hp0 hq'.ne'] at H
  have heq : (p/q-1)*q = p-q := by field_simp
  have heq' : (p/q*(Real.log p-Real.log q))*q = p*(Real.log p-Real.log q) := by
    field_simp
  rw [heq,heq'] at H
  unfold Real.negMulLog
  linarith

 
theorem finiteShannon_le_cross {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1)
    (hzero : ∀ a, q a = 0 → p a = 0) :
    finiteShannon p ≤ ∑ a, -p a * Real.log (q a) := by
  calc
    finiteShannon p ≤ ∑ a, (-p a * Real.log (q a) + q a-p a) :=
      Finset.sum_le_sum (fun a _ => negMulLog_le_cross (hp a) (hq a) (hzero a))
    _ = ∑ a, -p a * Real.log (q a) := by
      rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hp1,hq1]
      ring

 
theorem finiteShannon_joint_le {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    finiteShannon p ≤ finiteShannon (fun a => ∑ b, p (a,b)) +
      finiteShannon (fun b => ∑ a, p (a,b)) := by
  classical
  let r : α → ℝ := fun a => ∑ b, p (a,b)
  let c : β → ℝ := fun b => ∑ a, p (a,b)
  have hr a : 0 ≤ r a := Finset.sum_nonneg fun _ _ => hp _
  have hc b : 0 ≤ c b := Finset.sum_nonneg fun _ _ => hp _
  have hr1 : ∑ a, r a = 1 := by simpa [r,Fintype.sum_prod_type] using hp1
  have hc1 : ∑ b, c b = 1 := by
    change (∑ b, ∑ a, p (a,b)) = 1
    rw [Finset.sum_comm]
    simpa only [r] using hr1
  have hpr a b : p (a,b) ≤ r a := Finset.single_le_sum
    (fun j _ => hp (a,j)) (Finset.mem_univ b)
  have hpc a b : p (a,b) ≤ c b := Finset.single_le_sum
    (fun i _ => hp (i,b)) (Finset.mem_univ a)
  have hq1 : ∑ z : α × β, r z.1 * c z.2 = 1 := by
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,hc1,mul_one,hr1]
  have H := finiteShannon_le_cross hp (fun z => mul_nonneg (hr z.1) (hc z.2)) hp1 hq1
    (fun z hz => by
      rcases mul_eq_zero.mp hz with h | h
      · exact le_antisymm (h ▸ hpr z.1 z.2) (hp z)
      · exact le_antisymm (h ▸ hpc z.1 z.2) (hp z))
  refine H.trans_eq ?_
  have heq (a : α) (b : β) : -p (a,b)*Real.log (r a*c b) =
      -p (a,b)*Real.log (r a) + -p (a,b)*Real.log (c b) := by
    by_cases h : p (a,b) = 0
    · simp [h]
    have hpos := lt_of_le_of_ne (hp (a,b)) (Ne.symm h)
    rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le hpos (hpr a b)))
      (ne_of_gt (lt_of_lt_of_le hpos (hpc a b))),mul_add]
  simp only [Fintype.sum_prod_type,heq,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => -p (a,b)*Real.log (c b))]
  congr 1
  · simp only [finiteShannon,Real.negMulLog,r,← Finset.sum_mul,Finset.sum_neg_distrib]
  · simp only [finiteShannon,Real.negMulLog,c,← Finset.sum_mul,Finset.sum_neg_distrib]

 
theorem finiteShannon_le_log_card {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    finiteShannon p ≤ Real.log (Fintype.card α) := by
  classical
  have hn : 0 < Fintype.card α := by
    by_contra hn
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
    simp at hp1
  have hn' : (Fintype.card α : ℝ) ≠ 0 := by positivity
  have H := finiteShannon_le_cross hp
    (q := fun _ => (Fintype.card α : ℝ)⁻¹) (fun _ => by positivity) hp1
    (by simp [hn']) (fun _ h => (inv_ne_zero hn' h).elim)
  refine H.trans_eq ?_
  rw [← Finset.sum_mul,Finset.sum_neg_distrib,hp1,Real.log_inv]
  ring

 
def observationEntropy {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (P : Y → α) : ℝ :=
  finiteShannon (fun a => μ.real {y | P y = a})

lemma observation_distribution_sum {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    ∑ a, μ.real {y | P y = a} = 1 := by
  have hd : Pairwise (fun a b => Disjoint {y | P y = a} {y | P y = b}) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hab (hy.symm.trans hy')
  rw [← measureReal_iUnion_fintype hd hP]
  have heq : (⋃ a, {y | P y = a}) = Set.univ := by ext; simp
  rw [heq]; simp [Measure.real]

lemma observationEntropy_nonneg {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    0 ≤ observationEntropy μ P :=
  finiteShannon_nonneg (fun _ => measureReal_nonneg) (observation_distribution_sum μ P hP)

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal
namespace PrimeDegreePackets

lemma observationEntropy_equiv {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) (P : Y → α) (e : α ≃ β) :
    observationEntropy μ (fun y => e (P y)) = observationEntropy μ P := by
  classical
  unfold observationEntropy finiteShannon
  rw [← e.sum_comp]
  simp only [Equiv.apply_eq_iff_eq]

lemma observation_joint_row {Y α β : Type*} [MeasurableSpace Y]
    [Fintype β] (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (hQ : ∀ b, MeasurableSet {y | Q y = b})
    (a : α) :
    ∑ b, μ.real {y | (P y,Q y) = (a,b)} = μ.real {y | P y = a} := by
  have hd : Pairwise (fun b c => Disjoint {y | (P y,Q y) = (a,b)}
      {y | (P y,Q y) = (a,c)}) := by
    intro b c hbc
    rw [Set.disjoint_left]
    intro y hy hz
    exact hbc ((congrArg Prod.snd hy).symm.trans (congrArg Prod.snd hz))
  have hm b : MeasurableSet {y | (P y,Q y) = (a,b)} := by
    simpa only [Prod.mk.injEq,Set.ofPred_and] using (hP a).inter (hQ b)
  rw [← measureReal_iUnion_fintype hd hm]
  congr 1
  ext y
  simp

 
theorem observationEntropy_joint_le {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    observationEntropy μ (fun y => (P y,Q y)) ≤
      observationEntropy μ P + observationEntropy μ Q := by
  have hm (z : α × β) : MeasurableSet {y | (P y,Q y) = z} := by
    rcases z with ⟨a,b⟩
    simpa only [Prod.mk.injEq,Set.ofPred_and] using (hP a).inter (hQ b)
  have H := finiteShannon_joint_le (fun z =>
    measureReal_nonneg (μ := μ) (s := {y | (P y,Q y) = z}))
    (observation_distribution_sum μ (fun y => (P y,Q y)) hm)
  have hrow := observation_joint_row μ P Q hP hQ
  have hcol (b : β) : (∑ a, μ.real {y | (P y,Q y) = (a,b)}) = μ.real {y | Q y = b} := by
    convert observation_joint_row μ Q P hQ hP b using 1
    congr 1
    ext a
    congr 1
    ext y
    simp only [Prod.mk.injEq,and_comm]
  simpa only [hrow,hcol,observationEntropy] using H

lemma observationEntropy_comp_preserving {Y α : Type*} [MeasurableSpace Y]
    [Fintype α] (μ : Measure Y) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) {S : Y → Y} (hS : MeasurePreserving S μ μ) :
    observationEntropy μ (fun y => P (S y)) = observationEntropy μ P := by
  unfold observationEntropy finiteShannon
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (μ (S ⁻¹' {y | P y = a})).toReal = (μ {y | P y = a}).toReal
  rw [hS.measure_preimage (hP a).nullMeasurableSet]

 
def orbitName {Y α : Type*} (T : Y → Y) (P : Y → α) (N : ℕ) (y : Y) : Fin N → α :=
  fun j => P (T^[j] y)

lemma orbitName_measurable_fiber {Y α : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {P : Y → α}
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) (a : Fin N → α) :
    MeasurableSet {y | orbitName T P N y = a} := by
  have heq : {y | orbitName T P N y = a} = ⋂ j : Fin N, {y | P (T^[j] y) = a j} := by
    ext y
    simp [orbitName,funext_iff]
  rw [heq]
  exact MeasurableSet.iInter fun j => (hP (a j)).preimage (hT.iterate j)

lemma orbitName_add {Y α : Type*} (T : Y → Y) (P : Y → α) (m n : ℕ) :
    orbitName T P (m+n) = fun y => (Fin.appendEquiv m n)
      (orbitName T P m y,orbitName T P n (T^[m] y)) := by
  funext y
  apply (Fin.appendEquiv m n).symm.injective
  ext i
  · simp [orbitName]
  · simp only [Fin.appendEquiv_symm_apply,orbitName,
      Equiv.symm_apply_apply,Fin.val_natAdd]
    rw [Function.iterate_add_apply,← Function.iterate_add_apply,
      ← Function.iterate_add_apply,Nat.add_comm]

 
theorem orbitEntropy_subadditive {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Subadditive (fun N => observationEntropy μ (orbitName T P N)) := by
  intro m n
  change observationEntropy μ (orbitName T P (m+n)) ≤
    observationEntropy μ (orbitName T P m) + observationEntropy μ (orbitName T P n)
  rw [orbitName_add,observationEntropy_equiv]
  have H := observationEntropy_joint_le μ (orbitName T P m)
    (fun y => orbitName T P n (T^[m] y))
    (orbitName_measurable_fiber hT.measurable hP m)
    (fun a => (orbitName_measurable_fiber hT.measurable hP n a).preimage
      (hT.measurable.iterate m))
  rw [observationEntropy_comp_preserving μ _
    (orbitName_measurable_fiber hT.measurable hP n) (hT.iterate m)] at H
  exact H

 

def observationEntropyRate {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T : Y → Y) (P : Y → α) : ℝ :=
  sInf ((fun N : ℕ => observationEntropy μ (orbitName T P N)/(N:ℝ)) '' Set.Ici 1)

 
theorem tendsto_observationEntropyRate {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Tendsto (fun N : ℕ => observationEntropy μ (orbitName T P N)/(N:ℝ)) atTop
      (𝓝 (observationEntropyRate μ T P)) := by
  have h := orbitEntropy_subadditive μ hT P hP
  have hb : BddBelow (Set.range (fun N : ℕ => observationEntropy μ (orbitName T P N)/(N:ℝ))) := by
    refine ⟨0,?_⟩
    rintro _ ⟨N,rfl⟩
    exact div_nonneg (observationEntropy_nonneg μ _
      (orbitName_measurable_fiber hT.measurable hP N)) (Nat.cast_nonneg N)
  simpa only [Subadditive.lim,observationEntropyRate] using h.tendsto_lim hb

 

def measureEntropy {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (T : Y → Y) : ℝ≥0∞ :=
  ⨆ k : ℕ, ⨆ P : Y → Fin k, ⨆ (_hP : ∀ a, MeasurableSet {y | P y = a}),
    ENNReal.ofReal (observationEntropyRate μ T P)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma negMulLog_lower_of_le_exp {r B : ℝ} (hr : 0 ≤ r) (hB : r ≤ Real.exp (-B)) :
    B*r ≤ Real.negMulLog r := by
  by_cases h0 : r = 0
  · simp [h0]
  have hr' : 0 < r := lt_of_le_of_ne hr (Ne.symm h0)
  have H : Real.log r ≤ -B := by
    simpa only [Real.log_exp] using Real.log_le_log hr' hB
  have H' := mul_le_mul_of_nonneg_left H hr
  unfold Real.negMulLog
  nlinarith

 

theorem finiteShannon_split_lower {α : Type*} [Fintype α] {p r : α → ℝ}
    (_hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hr : ∀ a, 0 ≤ r a) (hrp : ∀ a, r a ≤ p a)
    (B : ℝ) (hB : ∀ a, r a ≤ Real.exp (-B)) :
    B*(∑ a, r a)-Real.log 2 ≤ finiteShannon p := by
  classical
  let q : α × Bool → ℝ := fun z => if z.2 then r z.1 else p z.1-r z.1
  have hq z : 0 ≤ q z := by
    rcases z with ⟨a,b⟩
    cases b <;> simp only [q,Bool.false_eq_true,↓reduceIte] <;> linarith [hr a,hrp a]
  have hrow a : ∑ b, q (a,b) = p a := by simp [q]
  have hq1 : ∑ z, q z = 1 := by simpa only [Fintype.sum_prod_type,hrow] using hp1
  have hqle z : q z ≤ 1 := by
    rw [← hq1]
    exact Finset.single_le_sum (fun z _ => hq z) (Finset.mem_univ z)
  have Hlow : B*(∑ a, r a) ≤ finiteShannon q := by
    rw [Finset.mul_sum]
    calc
      (∑ a, B*r a) ≤ ∑ a, Real.negMulLog (r a) :=
        Finset.sum_le_sum fun a _ => negMulLog_lower_of_le_exp (hr a) (hB a)
      _ ≤ ∑ a, (Real.negMulLog (p a-r a)+Real.negMulLog (r a)) := by
        apply Finset.sum_le_sum
        intro a _
        have H := Real.negMulLog_nonneg (hq (a,false)) (hqle (a,false))
        dsimp [q] at H
        linarith
      _ = finiteShannon q := by simp [finiteShannon,Fintype.sum_prod_type,q,add_comm]
  have Hjoint := finiteShannon_joint_le hq hq1
  simp only [hrow] at Hjoint
  have hcols : (∑ b, ∑ a, q (a,b)) = 1 := by
    rw [Finset.sum_comm]
    simpa only [hrow] using hp1
  have Hcol : finiteShannon (fun b => ∑ a, q (a,b)) ≤ Real.log 2 := by
    simpa using finiteShannon_le_log_card
      (fun b => Finset.sum_nonneg fun a _ => hq (a,b)) hcols
  linarith

lemma sum_good_observation_masses {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) {A : Set Y} (hA : MeasurableSet A) :
    (∑ a, μ.real (A ∩ {y | P y = a})) = μ.real A := by
  have hd : Pairwise (fun a b => Disjoint (A ∩ {y | P y = a}) (A ∩ {y | P y = b})) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro y hy hz
    exact hab (hy.2.symm.trans hz.2)
  rw [← measureReal_iUnion_fintype hd (fun a => hA.inter (hP a))]
  congr 1
  ext y
  simp

 

theorem observationEntropy_lower_of_good_atoms {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) {A : Set Y} (hA : MeasurableSet A)
    (B : ℝ) (hB : ∀ a, μ.real (A ∩ {y | P y = a}) ≤ Real.exp (-B)) :
    B*μ.real A-Real.log 2 ≤ observationEntropy μ P := by
  have H := finiteShannon_split_lower (p := fun a => μ.real {y | P y = a})
    (r := fun a => μ.real (A ∩ {y | P y = a}))
    (fun _ => measureReal_nonneg) (observation_distribution_sum μ P hP)
    (fun _ => measureReal_nonneg) (fun _ => measureReal_mono Set.inter_subset_right) B hB
  rw [sum_good_observation_masses μ P hP hA] at H
  exact H

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem observationEntropyRate_lower_of_good_atoms {Y α : Type*} [MeasurableSpace Y]
    [Fintype α] (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (A : ℕ → Set Y) (hA : ∀ N, MeasurableSet (A N))
    {c C w : ℝ} (hc : 0 ≤ c) (hC : 0 < C)
    (hw : ∀ᶠ N : ℕ in atTop, w ≤ μ.real (A N))
    (hsmall : ∀ᶠ N : ℕ in atTop, ∀ a : Fin N → α,
      μ.real (A N ∩ {y | orbitName T P N y = a}) ≤ C*Real.exp (-c*N)) :
    c*w ≤ observationEntropyRate μ T P := by
  let D : ℝ := |Real.log C| + Real.log 2
  have HN : ∀ᶠ N : ℕ in atTop,
      c*w-D/(N:ℝ) ≤ observationEntropy μ (orbitName T P N)/(N:ℝ) := by
    filter_upwards [hw,hsmall,eventually_ge_atTop (1:ℕ)] with N hwN hsN hN
    have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hexp : Real.exp (-(c*N-Real.log C)) = C*Real.exp (-c*N) := by
      rw [show -(c*(N:ℝ)-Real.log C)=Real.log C+(-c*N) by ring,Real.exp_add,
        Real.exp_log hC]
    have HL := observationEntropy_lower_of_good_atoms μ (orbitName T P N)
      (orbitName_measurable_fiber hT.measurable hP N) (hA N) (c*N-Real.log C)
      (fun a => (hsN a).trans_eq hexp.symm)
    have hmass0 : 0 ≤ μ.real (A N) := measureReal_nonneg
    have hmass1 : μ.real (A N) ≤ 1 := by
      have H := measureReal_mono (μ := μ) (Set.subset_univ (A N))
      simpa only [measureReal_def,measure_univ,ENNReal.toReal_one] using H
    have HH := mul_le_mul_of_nonneg_left hwN (mul_nonneg hc hn.le)
    have Hlog : Real.log C*μ.real (A N) ≤ |Real.log C| := by
      calc
        Real.log C*μ.real (A N) ≤ |Real.log C*μ.real (A N)| := le_abs_self _
        _ = |Real.log C| *μ.real (A N) := by rw [abs_mul,abs_of_nonneg hmass0]
        _ ≤ |Real.log C| := mul_le_of_le_one_right (abs_nonneg _) hmass1
    apply (le_div_iff₀ hn).mpr
    have Hcalc : (c*w-D/(N:ℝ))*(N:ℝ) = c*w*N-D := by field_simp
    rw [Hcalc]
    dsimp [D]
    nlinarith
  have hlimleft : Tendsto (fun N : ℕ => c*w-D/(N:ℝ)) atTop (𝓝 (c*w)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => D/(N:ℝ)) atTop (𝓝 0))
  exact le_of_tendsto_of_tendsto hlimleft (tendsto_observationEntropyRate μ hT P hP) HN

 

theorem measureEntropy_lower_of_good_atoms {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (k : ℕ) (P : Y → Fin k)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (A : ℕ → Set Y) (hA : ∀ N, MeasurableSet (A N))
    {c C w : ℝ} (hc : 0 ≤ c) (hC : 0 < C)
    (hw : ∀ᶠ N : ℕ in atTop, w ≤ μ.real (A N))
    (hsmall : ∀ᶠ N : ℕ in atTop, ∀ a : Fin N → Fin k,
      μ.real (A N ∩ {y | orbitName T P N y = a}) ≤ C*Real.exp (-c*N)) :
    ENNReal.ofReal (c*w) ≤ measureEntropy μ T := by
  exact le_iSup_of_le k (le_iSup_of_le P (le_iSup_of_le hP
    (ENNReal.ofReal_le_ofReal
      (observationEntropyRate_lower_of_good_atoms μ hT P hP A hA hc hC hw hsmall))))

end PrimeDegreePackets
end
end

end OAI
