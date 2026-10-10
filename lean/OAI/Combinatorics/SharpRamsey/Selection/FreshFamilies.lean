import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.TableCompositions

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset
open scoped Classical BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι→Type*} [∀ i,Fintype (α i)]

 def piLaw (p : ∀ i,Law (α i)) : Law (∀ i,α i) where
  mass z := ∏ i,(p i).mass (z i)
  nonneg z := prod_nonneg (fun i _=>(p i).nonneg (z i))
  total := by rw [←Fintype.prod_sum]; simp only [Law.total,prod_const_one]

abbrev Outside (i : ι) := ∀ j : {j // j≠i},α j

def outside (i : ι) (z : ∀ j,α j) : Outside (α:=α) i := fun j=>z j

def outsideLaw (p : ∀ i,Law (α i)) (i : ι) : Law (Outside (α:=α) i) :=
  piLaw (ι := {j : ι // j≠i}) (α := fun j=>α j.1) (fun j=>p j.1)

lemma family_mass_split (p : ∀ i,Law (α i)) (i : ι) (z : ∀ j,α j) :
    (piLaw p).mass z=(p i).mass (z i)*(outsideLaw p i).mass (outside i z) := by
  change (∏ j,(p j).mass (z j))=(p i).mass (z i)*
    (∏ j : {j : ι // j≠i},(p j).mass (z j))
  have he : (∏ j ∈ (univ : Finset ι).erase i,(p j).mass (z j))=
      ∏ j : {j : ι // j≠i},(p j).mass (z j) :=
    Finset.prod_subtype _ (by simp) _
  rw [←he]
  exact (mul_prod_erase univ (fun j=>(p j).mass (z j)) (mem_univ i)).symm

theorem family_integral (p : ∀ i,Law (α i)) (i : ι)
    (f : Outside (α:=α) i→α i→ℝ) :
    (∑ z,(piLaw p).mass z*f (outside i z) (z i)) =
      ∑ s,(outsideLaw p i).mass s*(∑ x,(p i).mass x*f s x) := by
  calc
    _ = ∑ z,(p i).mass (z i)*(outsideLaw p i).mass (outside i z)*f (outside i z) (z i) := by
      apply sum_congr rfl
      intro z _
      rw [family_mass_split]
    _ = ∑ y : α i×Outside (α:=α) i,(p i).mass y.1*(outsideLaw p i).mass y.2*f y.2 y.1 :=
        Fintype.sum_equiv (Equiv.piSplitAt i α) _ _ (fun _=>rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type,sum_comm]
      apply sum_congr rfl
      intro s _
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      ring

theorem ready_family_bound (p : ∀ i,Law (α i)) (i : ι)
    (Ready : Outside (α:=α) i→Prop) (f : Outside (α:=α) i→α i→ℝ)
    (B : Outside (α:=α) i→ℝ)
    (h : ∀ s,Ready s→(∑ x,(p i).mass x*f s x)≤B s) :
    (∑ z,(piLaw p).mass z*(if Ready (outside i z) then f (outside i z) (z i) else 0))≤
      ∑ s,(outsideLaw p i).mass s*(if Ready s then B s else 0) := by
  rw [family_integral p i (fun s x=>if Ready s then f s x else 0)]
  apply sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ ((outsideLaw p i).nonneg s)
  by_cases hs : Ready s
  · simpa only [ite_eq_left hs] using h s hs
  · simp only [ite_eq_right hs,mul_zero,sum_const_zero,le_refl]

theorem predictable_budget (p : ∀ i,Law (α i))
    (Ready : ∀ i,Outside (α:=α) i→Prop) (f : ∀ i,Outside (α:=α) i→α i→ℝ)
    (B : ℝ) (hB : 0≤B)
    (hlocal : ∀ i s,Ready i s→(∑ x,(p i).mass x*f i s x)≤B)
    (hunique : ∀ z,((univ.filter (fun i=>Ready i (outside i z))).card:ℝ)≤1) :
    (∑ z,(piLaw p).mass z *
      (∑ i,if Ready i (outside i z) then f i (outside i z) (z i) else 0))≤B := by
  have hi (i : ι) := ready_family_bound p i (Ready i) (f i) (fun _=>B) (hlocal i)
  have he (i : ι) :
      (∑ s,(outsideLaw p i).mass s*(if Ready i s then B else 0)) =
        ∑ z,(piLaw p).mass z*(if Ready i (outside i z) then B else 0) := by
    rw [family_integral p i (fun s _=>if Ready i s then B else 0)]
    apply sum_congr rfl
    intro s _
    rw [←sum_mul,(p i).total,one_mul]
  simp_rw [he] at hi
  calc
    _ ≤ ∑ z,(piLaw p).mass z*(∑ i,if Ready i (outside i z) then B else 0) := by
      calc
        _ = ∑ i,∑ z,(piLaw p).mass z *
            (if Ready i (outside i z) then f i (outside i z) (z i) else 0) := by
          simp_rw [mul_sum]
          rw [sum_comm]
        _ ≤ ∑ i,∑ z,(piLaw p).mass z *
            (if Ready i (outside i z) then B else 0) := sum_le_sum (fun i _=>hi i)
        _ = _ := by rw [sum_comm]; simp_rw [mul_sum]
    _ ≤ ∑ z,(piLaw p).mass z*B := by
      apply sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ ((piLaw p).nonneg z)
      rw [←sum_filter,sum_const,nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_right (hunique z) hB).trans_eq (one_mul B)
    _ = B := by rw [←sum_mul,(piLaw p).total,one_mul]

theorem exists_fixed_family {Ω : Type*} [Fintype Ω] (μ : Law Ω)
    (p : ∀ i,Law (α i)) (success : Ω→(∀i,α i)→Prop) (c : ℝ)
    (h : c≤∑ z,(piLaw p).mass z*(∑ ω,μ.mass ω*(if success ω z then 1 else 0))) :
    ∃ z,c≤∑ ω,μ.mass ω*(if success ω z then 1 else 0) := by
  by_contra! hn
  have hlt : (∑ z,(piLaw p).mass z*(∑ ω,μ.mass ω*(if success ω z then 1 else 0)))<c := by
    have hnzero : ∃ z,(piLaw p).mass z≠0 := by
      by_contra! hz
      have ht := (piLaw p).total
      simp_rw [hz,sum_const_zero] at ht
      norm_num at ht
    obtain ⟨z,hz⟩ := hnzero
    have hh := sum_lt_sum (fun y (_hy : y∈univ)=>
      mul_le_mul_of_nonneg_left (hn y).le ((piLaw p).nonneg y))
      ⟨z,mem_univ _,mul_lt_mul_of_pos_left (hn z) (lt_of_le_of_ne ((piLaw p).nonneg z) (Ne.symm hz))⟩
    simpa only [←sum_mul,(piLaw p).total,one_mul] using hh
  linarith

end
end SharpLogRamsey.PublicTables

end

end OAI
