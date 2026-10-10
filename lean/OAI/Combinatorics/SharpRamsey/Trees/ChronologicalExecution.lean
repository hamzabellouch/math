import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotExecution
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedSupportTrim

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset PublicTables SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {A B C Ξ I : Type*} [Fintype A] [Fintype B] [Fintype Ξ]
  [DecidableEq I] {α : I→Type*}

lemma card_mul_kernel_sum (Y : Finset A) (f : A→ℝ) :
    (Y.card:ℝ)*(∑ y,kernel Y y*f y)=∑ y∈Y,f y := by
  by_cases h : Y.Nonempty
  · have hc : (Y.card:ℝ)≠0 := by exact_mod_cast card_ne_zero.mpr h
    calc
      _ = ∑ y,if y∈Y then f y else 0 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro y _
        by_cases hy : y∈Y <;> simp [kernel,hy,hc]
      _ = _ := by simp
  · have he : Y=∅ := not_nonempty_iff_eq_empty.mp h
    simp [he]

omit [Fintype A] in
lemma sdiff_card_eq_sum (Y T : Finset A) :
    ((Y\T).card:ℝ) = ∑ y∈Y,if y∉T then (1:ℝ) else 0 := by
  rw [←sum_filter]
  have hf : Y.filter (fun y=>y∉T)=Y\T := by ext y; simp
  rw [hf]
  simp only [sum_const,nsmul_eq_mul,mul_one]

omit [Fintype A] [Fintype B] [DecidableEq I] in
lemma firstLoss_points (choose : ∀ i,α i→TreeDecoder.Domains A B→Option C)
    (mask : ∀ i,α i→TreeDecoder.CapReader A B C) (Y : Finset A)
    (i : I) (U : TreeDecoder.Domains A B) (z : α i) :
    firstLoss choose mask Y i U z = ∑ y∈Y,(choose i z U).elim 0
      (fun c=>if y∉(mask i z U c).1 then 1 else 0) := by
  cases h : choose i z U with
  | none=>simp [firstLoss,h]
  | some c=>simp only [firstLoss,h,Option.elim_some]; exact sdiff_card_eq_sum _ _

omit [Fintype A] [Fintype B] [DecidableEq I] in
lemma secondLoss_points (choose : ∀ i,α i→TreeDecoder.Domains A B→Option C)
    (mask : ∀ i,α i→TreeDecoder.CapReader A B C) (Y : Finset B)
    (i : I) (U : TreeDecoder.Domains A B) (z : α i) :
    secondLoss choose mask Y i U z = ∑ y∈Y,(choose i z U).elim 0
      (fun c=>if y∉(mask i z U c).2 then 1 else 0) := by
  cases h : choose i z U with
  | none=>simp [secondLoss,h]
  | some c=>simp only [secondLoss,h,Option.elim_some]; exact sdiff_card_eq_sum _ _

end
end SharpLogRamsey.FreshExecution

namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder FreshExecution SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

abbrev ChronoDomains := Domains (Projectivization K (Module.Dual K V)) (Projectivization K V)

def chronoRead (b : ℝ) (z : Banks (K:=K) (V:=V) b) :
    CapReader (Projectivization K (Module.Dual K V)) (Projectivization K V) (Code (K:=K) (V:=V) b) :=
  fun U c=>(read b z.1 z.2 U.swap c).swap

def chronoMask (b : ℝ) (z : Banks (K:=K) (V:=V) b) :
    CapReader (Projectivization K (Module.Dual K V)) (Projectivization K V) (Code (K:=K) (V:=V) b) :=
  fun U c=>(mask b z.1 z.2 U.swap c).swap

omit [Finite K] in
lemma chronoRead_first (b : ℝ) (z : Banks (K:=K) (V:=V) b)
    (U : ChronoDomains (K:=K) (V:=V)) (c : Code (K:=K) (V:=V) b) :
    (chronoRead b z U c).1=U.1∩(chronoMask b z U c).1 :=
  read_mask_second b z.1 z.2 U.swap c

omit [Finite K] in
lemma chronoRead_second (b : ℝ) (z : Banks (K:=K) (V:=V) b)
    (U : ChronoDomains (K:=K) (V:=V)) (c : Code (K:=K) (V:=V) b) :
    (chronoRead b z U c).2=U.2∩(chronoMask b z U c).2 :=
  read_mask_first b z.1 z.2 U.swap c

variable {n : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

def Book.chronoChoose (s : Original (K:=K) (V:=V) n b)
    (z : Banks (K:=K) (V:=V) b) (U : ChronoDomains (K:=K) (V:=V)) :
    Option (Code (K:=K) (V:=V) b) := book.choose hdim hτ hτsmall s z U.swap

theorem Book.first_loss_bound {I : Type*} [DecidableEq I]
    (s : I→Original (K:=K) (V:=V) n b) (i : I)
    (Y : Finset (Projectivization K (Module.Dual K V)))
    (U : ChronoDomains (K:=K) (V:=V)) :
    (∑ z,(banksLaw b).mass z*firstLoss (fun i=>book.chronoChoose hdim hτ hτsmall (s i))
      (fun _=>chronoMask b) Y i U z) ≤
      12*(Nat.card K:ℝ)*Y.card*pairing (kernel Y) (kernel (s i).A)
        (fun y x=>if y.rep x.rep=0 then 1 else 0) := by
  simp_rw [firstLoss_points,mul_sum]
  rw [sum_comm]
  calc
    _ ≤ ∑ y∈Y,12*(Nat.card K:ℝ)*∑ x,kernel (s i).A x *
        (if y.rep x.rep=0 then 1 else 0) := by
      apply sum_le_sum
      intro y hy
      exact book.dual_exclusion hdim hτ hτsmall (s i) U.swap y
    _ = 12*(Nat.card K:ℝ)*(∑ y∈Y,∑ x,kernel (s i).A x *
        (if y.rep x.rep=0 then 1 else 0)) := by rw [mul_sum]
    _ = 12*(Nat.card K:ℝ)*(Y.card*pairing (kernel Y) (kernel (s i).A)
        (fun y x=>if y.rep x.rep=0 then 1 else 0)) := by
      congr 1
      have he : pairing (kernel Y) (kernel (s i).A) (fun y x=>if y.rep x.rep=0 then 1 else 0) =
          ∑ y,kernel Y y*(∑ x,kernel (s i).A x*(if y.rep x.rep=0 then 1 else 0)) := by
        simp only [pairing,mul_sum,mul_assoc]
      rw [he,card_mul_kernel_sum]
    _ = _ := by ring

theorem Book.second_loss_bound {I : Type*} [DecidableEq I]
    (s : I→Original (K:=K) (V:=V) n b) (i : I)
    (Y : Finset (Projectivization K V))
    (U : ChronoDomains (K:=K) (V:=V)) :
    (∑ z,(banksLaw b).mass z*secondLoss (fun i=>book.chronoChoose hdim hτ hτsmall (s i))
      (fun _=>chronoMask b) Y i U z) ≤
      12*(Nat.card K:ℝ)*Y.card*pairing (kernel (s i).B) (kernel Y)
        (fun y x=>if y.rep x.rep=0 then 1 else 0) := by
  simp_rw [secondLoss_points,mul_sum]
  rw [sum_comm]
  calc
    _ ≤ ∑ x∈Y,12*(Nat.card K:ℝ)*∑ y,kernel (s i).B y *
        (if y.rep x.rep=0 then 1 else 0) := by
      apply sum_le_sum
      intro x hx
      exact book.primal_exclusion hdim hτ hτsmall (s i) U.swap x
    _ = 12*(Nat.card K:ℝ)*(∑ x∈Y,∑ y,kernel (s i).B y *
        (if y.rep x.rep=0 then 1 else 0)) := by rw [mul_sum]
    _ = 12*(Nat.card K:ℝ)*(Y.card*pairing (kernel (s i).B) (kernel Y)
        (fun y x=>if y.rep x.rep=0 then 1 else 0)) := by
      congr 1
      rw [pairing_reverse]
      have he : pairing (kernel Y) (kernel (s i).B) (fun x y=>if y.rep x.rep=0 then 1 else 0) =
          ∑ x,kernel Y x*(∑ y,kernel (s i).B y*(if y.rep x.rep=0 then 1 else 0)) := by
        simp only [pairing,mul_sum,mul_assoc]
      rw [he,card_mul_kernel_sum]
    _ = _ := by ring
end
end SharpLogRamsey.ActualPivot

end

end OAI
