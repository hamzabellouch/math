import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.ChronologicalExecution
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedFailureBudget

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence PublicTables FreshExecution TreeDecoder SupportMixtures BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

local instance banksFintype (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

omit [Finite K] [FiniteDimensional K V] in
lemma banks_nonempty (b : ℝ) : Nonempty (Banks (K:=K) (V:=V) b) := by
  by_contra h
  have : IsEmpty (Banks (K:=K) (V:=V) b) := not_nonempty_iff.mp h
  have hh := (banksLaw (K:=K) (V:=V) b).total
  simp at hh

def density (S : Finset (Projectivization K (Module.Dual K V)))
    (T : Finset (Projectivization K V)) : ℝ :=
  pairing (kernel S) (kernel T) (fun y x=>if y.rep x.rep=0 then 1 else 0)

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma density_nonneg (S : Finset (Projectivization K (Module.Dual K V)))
    (T : Finset (Projectivization K V)) : 0≤density S T := by
  unfold density pairing
  exact sum_nonneg (fun y _=>sum_nonneg (fun x _=>
    mul_nonneg (mul_nonneg (kernel_nonneg _ _) (kernel_nonneg _ _)) (by dsimp only; split_ifs <;> norm_num)))

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma density_eq_count (S : Finset (Projectivization K (Module.Dual K V)))
    (T : Finset (Projectivization K V)) :
    density S T=(incidenceCount T S:ℝ)/((T.card:ℝ)*S.card) := by
  unfold density
  rw [Selection.pairing_reverse,kernel_incidence,incidenceCount_eq_card]
  rfl

variable {n : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

omit [Fintype I] [DecidableEq I] in
lemma Book.ready_failure_chrono (s : I→Original (K:=K) (V:=V) n b) (i : I)
    (U : ChronoDomains (K:=K) (V:=V)) :
    (∑ z,(banksLaw (K:=K) (V:=V) b).mass z*readyFailure
      (fun i=>book.chronoChoose hdim hτ hτsmall (s i)) (s i).B (s i).A
      ((incidenceCount (s i).A (s i).B:ℝ)>τ*((s i).A.card:ℝ)*(s i).B.card/Nat.card K) i U z) ≤
        2*exp (-(Nat.card K:ℝ)) := by
  by_cases hr : (s i).Ready τ U.swap
  · have hh := book.ready_failure hdim hτ hτsmall (s i) U.swap hr
    have hB : ¬((s i).B∩U.1).card<(9/10:ℝ)*(s i).B.card := not_lt.mpr hr.2.1
    have hA : ¬((s i).A∩U.2).card<(9/10:ℝ)*(s i).A.card := not_lt.mpr hr.1
    have hD : ¬τ*((s i).A.card:ℝ)*(s i).B.card/Nat.card K<
        (incidenceCount (s i).A (s i).B:ℝ) := not_lt.mpr hr.2.2
    simp only [readyFailure,hB,hA,hD,not_false_eq_true,and_self,ite_true,
      trialFailure,Book.chronoChoose]
    convert hh using 1
    rfl
  · have hn : ¬(¬((s i).B∩U.1).card<(9/10:ℝ)*(s i).B.card ∧
        ¬((s i).A∩U.2).card<(9/10:ℝ)*(s i).A.card ∧
        ¬τ*((s i).A.card:ℝ)*(s i).B.card/Nat.card K<(incidenceCount (s i).A (s i).B:ℝ)) := by
      intro hh
      apply hr
      exact ⟨not_lt.mp hh.2.1,not_lt.mp hh.1,not_lt.mp hh.2.2⟩
    simp only [readyFailure,ite_eq_right hn,mul_zero,sum_const_zero]
    positivity

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem original_density_rejection (μ : Law Ω) (s : Ω→Original (K:=K) (V:=V) n b)
    (hτpos : 0<τ) (E : ℝ)
    (hmean : (∑ ω,μ.mass ω*density (s ω).B (s ω).A)≤E) :
    (∑ ω,μ.mass ω*(if τ*((s ω).A.card:ℝ)*(s ω).B.card/Nat.card K<
      (incidenceCount (s ω).A (s ω).B:ℝ) then 1 else 0))≤(Nat.card K:ℝ)*E/τ := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
  have hpoint (ω : Ω) : (if τ*((s ω).A.card:ℝ)*(s ω).B.card/Nat.card K<
      (incidenceCount (s ω).A (s ω).B:ℝ) then (1:ℝ) else 0)≤(Nat.card K:ℝ)*density (s ω).B (s ω).A/τ := by
    split_ifs with hh
    · have ha : (0:ℝ)<(s ω).A.card := by exact_mod_cast card_pos.mpr (s ω).nonemptyA
      have hb : (0:ℝ)<(s ω).B.card := by exact_mod_cast card_pos.mpr (s ω).nonemptyB
      rw [density_eq_count]
      apply le_of_lt
      apply (lt_div_iff₀ hτpos).mpr
      have hp := (div_lt_iff₀ hq).mp hh
      rw [←mul_div_assoc]
      apply (lt_div_iff₀ (mul_pos ha hb)).mpr
      convert hp using 1 <;> ring
    · exact div_nonneg (mul_nonneg hq.le (density_nonneg _ _)) hτpos.le
  calc
    _ ≤ ∑ ω,μ.mass ω*((Nat.card K:ℝ)*density (s ω).B (s ω).A/τ) :=
      sum_le_sum (fun ω _=>mul_le_mul_of_nonneg_left (hpoint ω) (μ.nonneg ω))
    _ = (Nat.card K:ℝ)*(∑ ω,μ.mass ω*density (s ω).B (s ω).A)/τ := by
      simp only [mul_sum,sum_div]
      apply sum_congr rfl
      intros
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmean hq.le) hτpos.le

theorem Book.first_trim (μ : Law Ω) (s : Ω→I→Original (K:=K) (V:=V) n b)
    (target : I) (t : BinaryTree I) (U : ChronoDomains (K:=K) (V:=V))
    (ht : Separated t) (hmem : target∈labels t) (hU : ∀ ω,(s ω target).B⊆U.1)
    (E : ℝ) (hE : 0≤E)
    (hmean : ∀ i∈leftPath target t,(∑ ω,μ.mass ω*density (s ω target).B (s ω i).A)≤E) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      (if firstTrim (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i))
        (fun _=>chronoRead b) (s ω target).B target t U z then (1:ℝ) else 0)))≤
      10*t.height*(12*(Nat.card K:ℝ)*E) := by
  apply original_first_trim μ (fun _=>banksLaw (K:=K) (V:=V) b) (fun _=>(banks_nonempty (K:=K) (V:=V) b).some)
    (fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)) (fun _ _=>chronoRead b)
    (fun _ _=>chronoMask b) (fun _ _=>chronoRead_first b)
    target (fun ω=>(s ω target).B) (fun ω=>(s ω target).nonemptyB) t U ht hmem hU
    (fun ω i=>12*(Nat.card K:ℝ)*(s ω target).B.card*density (s ω target).B (s ω i).A)
    (fun ω i _=>mul_nonneg (by positivity) (density_nonneg _ _))
    (fun ω i _=>book.first_loss_bound hdim hτ hτsmall (s ω) i (s ω target).B)
    (12*(Nat.card K:ℝ)*E) (by positivity)
  intro i hi
  have hc (ω : Ω) : ((s ω target).B.card:ℝ)≠0 := by
    exact_mod_cast card_ne_zero.mpr (s ω target).nonemptyB
  have he (ω : Ω) : (12*(Nat.card K:ℝ)*(s ω target).B.card*density (s ω target).B (s ω i).A)/
      (s ω target).B.card = 12*(Nat.card K:ℝ)*density (s ω target).B (s ω i).A := by
    field_simp [hc ω]
  simp only [he]
  calc
    _ = 12*(Nat.card K:ℝ)*(∑ ω,μ.mass ω*density (s ω target).B (s ω i).A) := by
      rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmean i hi) (by positivity)

theorem Book.second_trim (μ : Law Ω) (s : Ω→I→Original (K:=K) (V:=V) n b)
    (target : I) (t : BinaryTree I) (U : ChronoDomains (K:=K) (V:=V))
    (ht : Separated t) (hmem : target∈labels t) (hU : ∀ ω,(s ω target).A⊆U.2)
    (E : ℝ) (hE : 0≤E)
    (hmean : ∀ i∈rightPath target t,(∑ ω,μ.mass ω*density (s ω i).B (s ω target).A)≤E) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      (if secondTrim (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i))
        (fun _=>chronoRead b) (s ω target).A target t U z then (1:ℝ) else 0)))≤
      10*t.height*(12*(Nat.card K:ℝ)*E) := by
  apply original_second_trim μ (fun _=>banksLaw (K:=K) (V:=V) b) (fun _=>(banks_nonempty (K:=K) (V:=V) b).some)
    (fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)) (fun _ _=>chronoRead b)
    (fun _ _=>chronoMask b) (fun _ _=>chronoRead_second b)
    target (fun ω=>(s ω target).A) (fun ω=>(s ω target).nonemptyA) t U ht hmem hU
    (fun ω i=>12*(Nat.card K:ℝ)*(s ω target).A.card*density (s ω i).B (s ω target).A)
    (fun ω i _=>mul_nonneg (by positivity) (density_nonneg _ _))
    (fun ω i _=>book.second_loss_bound hdim hτ hτsmall (s ω) i (s ω target).A)
    (12*(Nat.card K:ℝ)*E) (by positivity)
  intro i hi
  have hc (ω : Ω) : ((s ω target).A.card:ℝ)≠0 := by
    exact_mod_cast card_ne_zero.mpr (s ω target).nonemptyA
  have he (ω : Ω) : (12*(Nat.card K:ℝ)*(s ω target).A.card*density (s ω i).B (s ω target).A)/
      (s ω target).A.card = 12*(Nat.card K:ℝ)*density (s ω i).B (s ω target).A := by
    field_simp [hc ω]
  simp only [he]
  calc
    _ = 12*(Nat.card K:ℝ)*(∑ ω,μ.mass ω*density (s ω i).B (s ω target).A) := by
      rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmean i hi) (by positivity)

theorem Book.deletion_loss (μ : Law Ω) (s : Ω→I→Original (K:=K) (V:=V) n b)
    (target : I) (t : BinaryTree I) (U : ChronoDomains (K:=K) (V:=V))
    (ht : Separated t) (hmem : target∈labels t)
    (hU : ∀ ω,∀ i∈labels t,(s ω i).B⊆U.1 ∧ (s ω i).A⊆U.2)
    (hτpos : 0<τ) (E : ℝ) (hE : 0≤E)
    (hfirst : ∀ i∈plannedPath target t,∀ j∈leftPath i t,
      (∑ ω,μ.mass ω*density (s ω i).B (s ω j).A)≤E)
    (hsecond : ∀ i∈plannedPath target t,∀ j∈rightPath i t,
      (∑ ω,μ.mass ω*density (s ω j).B (s ω i).A)≤E)
    (hself : ∀ i∈plannedPath target t,(∑ ω,μ.mass ω*density (s ω i).B (s ω i).A)≤E) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      (1-pivotSuccess (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i))
        (fun _=>chronoRead b) target t U z)))≤
      20*(12*(Nat.card K:ℝ)*E)*t.height^2+
        ((Nat.card K:ℝ)*E/τ+2*exp (-(Nat.card K:ℝ)))*t.height := by
  apply original_deletion_quadratic μ (fun _=>banksLaw (K:=K) (V:=V) b)
    (fun _=>(banks_nonempty (K:=K) (V:=V) b).some)
    (fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)) (fun _ _=>chronoRead b)
    (fun ω i=>(s ω i).B) (fun ω i=>(s ω i).A)
    (fun ω i=>τ*((s ω i).A.card:ℝ)*(s ω i).B.card/Nat.card K<
      (incidenceCount (s ω i).A (s ω i).B:ℝ)) target t U ht hmem
    (12*(Nat.card K:ℝ)*E) ((Nat.card K:ℝ)*E/τ) (2*exp (-(Nat.card K:ℝ)))
    (by positivity) (by positivity) (by positivity)
  · intro i hi
    exact book.first_trim hdim hτ hτsmall μ s i t U ht (plannedPath_subset target t hi)
      (fun ω=>(hU ω i (plannedPath_subset target t hi)).1) E hE (hfirst i hi)
  · intro i hi
    exact book.second_trim hdim hτ hτsmall μ s i t U ht (plannedPath_subset target t hi)
      (fun ω=>(hU ω i (plannedPath_subset target t hi)).2) E hE (hsecond i hi)
  · intro i hi
    exact original_density_rejection μ (fun ω=>s ω i) hτpos E (hself i hi)
  · intro i hi ω V
    exact book.ready_failure_chrono hdim hτ hτsmall (s ω) i V

end
end SharpLogRamsey.ActualPivot

end

end OAI
