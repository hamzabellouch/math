import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.OriginalTreeLoss
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedGoodTarget

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

local instance targetBanksFintype (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

def firstTargetDensity (good : Prop) (y : Projectivization K (Module.Dual K V))
    (T : Finset (Projectivization K V)) : ℝ :=
  if good then ∑ x,kernel T x*(if y.rep x.rep=0 then 1 else 0) else 0

def secondTargetDensity (good : Prop) (x : Projectivization K V)
    (S : Finset (Projectivization K (Module.Dual K V))) : ℝ :=
  if good then ∑ y,kernel S y*(if y.rep x.rep=0 then 1 else 0) else 0

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma firstTargetDensity_nonneg (good : Prop) (y : Projectivization K (Module.Dual K V))
    (T : Finset (Projectivization K V)) : 0≤firstTargetDensity good y T := by
  unfold firstTargetDensity
  split_ifs
  · exact sum_nonneg (fun x _=>mul_nonneg (kernel_nonneg _ _) (by split_ifs <;> norm_num))
  · exact le_rfl

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma secondTargetDensity_nonneg (good : Prop) (x : Projectivization K V)
    (S : Finset (Projectivization K (Module.Dual K V))) : 0 ≤ secondTargetDensity good x S := by
  unfold secondTargetDensity
  split_ifs
  · exact sum_nonneg (fun y _=>mul_nonneg (kernel_nonneg _ _) (by split_ifs <;> norm_num))
  · exact le_rfl

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma firstTargetDensity_eq (good : Prop) (y : Projectivization K (Module.Dual K V))
    (T : Finset (Projectivization K V)) :
    ((goodSingleton good y).card:ℝ)*density (goodSingleton good y) T=firstTargetDensity good y T := by
  have he : density (goodSingleton good y) T =
      ∑ y',kernel (goodSingleton good y) y' * (∑ x,kernel T x*(if y'.rep x.rep=0 then 1 else 0)) := by
    simp only [density,pairing,mul_sum,mul_assoc]
  rw [he,card_mul_kernel_sum]
  by_cases hg : good <;> simp [goodSingleton,hg,firstTargetDensity]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma secondTargetDensity_eq (good : Prop) (x : Projectivization K V)
    (S : Finset (Projectivization K (Module.Dual K V))) :
    ((goodSingleton good x).card:ℝ)*density S (goodSingleton good x)=secondTargetDensity good x S := by
  have he : density S (goodSingleton good x) =
      ∑ x',kernel (goodSingleton good x) x' * (∑ y,kernel S y*(if y.rep x'.rep=0 then 1 else 0)) := by
    unfold density
    rw [Selection.pairing_reverse]
    simp only [pairing,mul_sum,mul_assoc]
  rw [he,card_mul_kernel_sum]
  by_cases hg : good <;> simp [goodSingleton,hg,secondTargetDensity]

variable {n : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

theorem Book.target_loss (μ : Law Ω) (s : Ω→I→Original (K:=K) (V:=V) n b)
    (target : I) (t : BinaryTree I) (U : ChronoDomains (K:=K) (V:=V))
    (ht : Separated t) (hmem : target∈labels t)
    (hU : ∀ ω,∀ i∈labels t,(s ω i).B⊆U.1 ∧ (s ω i).A⊆U.2)
    (goodA goodB : Ω→Prop) (a : Ω→Projectivization K (Module.Dual K V))
    (c : Ω→Projectivization K V) (haU : ∀ ω,a ω∈U.1) (hcU : ∀ ω,c ω∈U.2)
    (hτpos : 0<τ) (E EA EB δA δB : ℝ) (hE : 0≤E) (hEA : 0≤EA) (hEB : 0≤EB)
    (hfirst : ∀ i∈plannedPath target t,∀ j∈leftPath i t,
      (∑ ω,μ.mass ω*density (s ω i).B (s ω j).A)≤E)
    (hsecond : ∀ i∈plannedPath target t,∀ j∈rightPath i t,
      (∑ ω,μ.mass ω*density (s ω j).B (s ω i).A)≤E)
    (hself : ∀ i∈plannedPath target t,(∑ ω,μ.mass ω*density (s ω i).B (s ω i).A)≤E)
    (hmeanA : ∀ i∈insert target (leftPath target t),
      (∑ ω,μ.mass ω*firstTargetDensity (goodA ω) (a ω) (s ω i).A)≤EA)
    (hmeanB : ∀ i∈insert target (rightPath target t),
      (∑ ω,μ.mass ω*secondTargetDensity (goodB ω) (c ω) (s ω i).B)≤EB)
    (hbadA : (∑ ω,μ.mass ω*(if goodA ω then (0:ℝ) else 1))≤δA)
    (hbadB : (∑ ω,μ.mass ω*(if goodB ω then (0:ℝ) else 1))≤δB) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      targetFailure (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i))
        (fun _=>chronoRead b) (a ω) (c ω) target t U z))≤
      20*(12*(Nat.card K:ℝ)*E)*t.height^2+
        ((Nat.card K:ℝ)*E/τ+2*exp (-(Nat.card K:ℝ)))*t.height+
        δA+δB+((t.height:ℝ)+1)*(12*(Nat.card K:ℝ)*EA+12*(Nat.card K:ℝ)*EB) := by
  apply original_good_target_loss μ (fun _=>banksLaw (K:=K) (V:=V) b)
    (fun _=>(banks_nonempty (K:=K) (V:=V) b).some)
    (fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)) (fun _ _=>chronoRead b)
    (fun _ _=>chronoMask b) (fun _ _=>chronoRead_first b) (fun _ _=>chronoRead_second b)
    goodA goodB a c target t U ht hmem haU hcU
    (fun ω i=>12*(Nat.card K:ℝ)*firstTargetDensity (goodA ω) (a ω) (s ω i).A)
    (fun ω i=>12*(Nat.card K:ℝ)*secondTargetDensity (goodB ω) (c ω) (s ω i).B)
    (12*(Nat.card K:ℝ)*EA) (12*(Nat.card K:ℝ)*EB) _ δA δB (by positivity) (by positivity)
  · intros; exact mul_nonneg (by positivity) (firstTargetDensity_nonneg _ _ _)
  · intros; exact mul_nonneg (by positivity) (secondTargetDensity_nonneg _ _ _)
  · intro ω i hi U
    have hh := book.first_loss_bound hdim hτ hτsmall (s ω) i (goodSingleton (goodA ω) (a ω)) U
    change _≤12*(Nat.card K:ℝ)*_ * density _ _ at hh
    rw [mul_assoc,firstTargetDensity_eq] at hh
    exact hh
  · intro ω i hi U
    have hh := book.second_loss_bound hdim hτ hτsmall (s ω) i (goodSingleton (goodB ω) (c ω)) U
    change _≤12*(Nat.card K:ℝ)*_ * density _ _ at hh
    rw [mul_assoc,secondTargetDensity_eq] at hh
    exact hh
  · intro i hi
    calc
      _ = 12*(Nat.card K:ℝ)*(∑ ω,μ.mass ω*firstTargetDensity (goodA ω) (a ω) (s ω i).A) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmeanA i hi) (by positivity)
  · intro i hi
    calc
      _ = 12*(Nat.card K:ℝ)*(∑ ω,μ.mass ω*secondTargetDensity (goodB ω) (c ω) (s ω i).B) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmeanB i hi) (by positivity)
  · exact hbadA
  · exact hbadB
  · exact book.deletion_loss hdim hτ hτsmall μ s target t U ht hmem hU hτpos E hE hfirst hsecond hself

end
end SharpLogRamsey.ActualPivot

end

end OAI
