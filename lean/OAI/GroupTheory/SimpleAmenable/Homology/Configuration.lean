import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.IntegralHomologyFunctorial

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConfigurationSupport
open Classical Finsupp
namespace ConfigurationChains
variable {V : Type*}

theorem linear_expansion (f : Chain V →ₗ[ℤ] Chain V) (c : Chain V) :
    f c=c.sum (fun l n => n • f (single l 1)) := by
  conv_lhs => rw [← Finsupp.sum_single c]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro l hl
  rw [←map_smul,Finsupp.smul_single,smul_eq_mul,mul_one]

theorem linear_support_subset (f : Chain V →ₗ[ℤ] Chain V) (c : Chain V) :
    (f c).support⊆c.support.biUnion (fun l => (f (single l 1)).support) := by
  rw [linear_expansion f c]
  intro s hs
  obtain ⟨l,hl,hs⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hs)
  exact Finset.mem_biUnion.mpr ⟨l,hl,Finsupp.support_smul hs⟩

theorem vertices_linear_subset (f : Chain V →ₗ[ℤ] Chain V) (c : Chain V) :
    vertices (f c)⊆c.support.biUnion (fun l => vertices (f (single l 1))) := by
  intro v hv
  obtain ⟨s,hs,hv⟩ := mem_vertices.mp hv
  obtain ⟨l,hl,hs⟩ := Finset.mem_biUnion.mp (linear_support_subset f c hs)
  exact Finset.mem_biUnion.mpr ⟨l,hl,mem_vertices.mpr ⟨s,hs,hv⟩⟩

theorem vertices_linear_card (f : Chain V →ₗ[ℤ] Chain V) (c : Chain V)
    (b : ℕ) (hb : ∀l∈c.support,(vertices (f (single l 1))).card≤b) :
    (vertices (f c)).card≤c.support.card*b := by
  calc
    _ ≤ (c.support.biUnion (fun l => vertices (f (single l 1)))).card :=
      Finset.card_le_card (vertices_linear_subset f c)
    _ ≤ ∑l∈c.support,(vertices (f (single l 1))).card := Finset.card_biUnion_le
    _ ≤ ∑l∈c.support,b := Finset.sum_le_sum hb
    _ = _ := by simp

def Admissible (R : V → V → Prop) (n : ℕ) (c : Chain V) : Prop :=
  ∀l∈c.support,List.Pairwise R l ∧ l.length=n

@[simp] theorem admissible_zero (R : V → V → Prop) (n : ℕ) :
    Admissible R n (0 : Chain V) := by simp [Admissible]

theorem admissible_single {R : V → V → Prop} {n : ℕ} {l : List V}
    (hl : List.Pairwise R l) (hn : l.length=n) (k : ℤ) :
    Admissible R n (single l k) := by
  intro s hs
  have he : s=l := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
  subst s
  exact ⟨hl,hn⟩

theorem admissible_sub {R : V → V → Prop} {n : ℕ} {c d : Chain V}
    (hc : Admissible R n c) (hd : Admissible R n d) : Admissible R n (c-d) := by
  intro l hl
  rcases Finset.mem_union.mp (Finsupp.support_sub hl) with hl|hl
  · exact hc l hl
  · exact hd l hl

theorem admissible_linear {R : V → V → Prop} {n k : ℕ} {c : Chain V}
    (f : Chain V →ₗ[ℤ] Chain V) (hc : Admissible R n c)
    (hf : ∀l,List.Pairwise R l → l.length=n → Admissible R k (f (single l 1))) :
    Admissible R k (f c) := by
  intro s hs
  obtain ⟨l,hl,hs⟩ := Finset.mem_biUnion.mp (linear_support_subset f c hs)
  exact hf l (hc l hl).1 (hc l hl).2 s hs

theorem admissible_faceSum {R : V → V → Prop} {n : ℕ} {l : List V}
    (hl : List.Pairwise R l) (hn : l.length=n+1) : Admissible R n (faceSum l) := by
  intro s hs
  obtain ⟨hsub,hlen⟩ := faceSum_support hs
  exact ⟨hl.sublist hsub,by omega⟩

theorem admissible_boundary {R : V → V → Prop} {n : ℕ} {c : Chain V}
    (hc : Admissible R (n+1) c) : Admissible R n (boundary c) := by
  apply admissible_linear boundary hc
  intro l hl hn
  simpa using admissible_faceSum hl hn

theorem admissible_cone {R : V → V → Prop} {n : ℕ} {c : Chain V}
    (hc : Admissible R n c) (v : V) (hv : ∀w∈vertices c,R v w) :
    Admissible R (n+1) (cone v c) := by
  intro l hl
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp (cone_support_subset v c hl)
  have h := hc s hs
  refine ⟨List.pairwise_cons.mpr ⟨?_,h.1⟩,by simp [h.2]⟩
  intro w hw
  exact hv w (mem_vertices.mpr ⟨s,hs,hw⟩)

theorem vertices_boundary_subset (c : Chain V) : vertices (boundary c)⊆vertices c := by
  intro v hv
  obtain ⟨l,hl,hv⟩ := Finset.mem_biUnion.mp (vertices_linear_subset boundary c hv)
  simp only [boundary_single,one_smul] at hv
  obtain ⟨s,hs,hv⟩ := mem_vertices.mp hv
  exact mem_vertices.mpr ⟨l,hl,(faceSum_support hs).1.subset hv⟩

theorem linear_eq_on_admissible {R : V → V → Prop} {n : ℕ}
    (f g : Chain V →ₗ[ℤ] Chain V)
    (h : ∀l,List.Pairwise R l → l.length=n → f (single l 1)=g (single l 1))
    {c : Chain V} (hc : Admissible R n c) : f c=g c := by
  rw [linear_expansion f c,linear_expansion g c]
  apply Finsupp.sum_congr
  intro l hl
  rw [h l (hc l hl).1 (hc l hl).2]

end ConfigurationChains
end ConfigurationSupport

section BoundedConfigurationContraction
open Classical Finsupp
namespace ConfigurationChains
variable {V : Type*} {R : V → V → Prop}

structure Step (R : V → V → Prop) (n b : ℕ) where
  previous : Chain V →ₗ[ℤ] Chain V
  current : Chain V →ₗ[ℤ] Chain V
  equation : ∀c,Admissible R n c → boundary (current c)+previous (boundary c)=c
  admissible : ∀l,List.Pairwise R l → l.length=n →
    Admissible R (n+1) (current (single l 1))
  bounded : ∀l,List.Pairwise R l → l.length=n →
    (vertices (current (single l 1))).card≤b

namespace Step
variable {n b : ℕ} (D : Step R n b)

noncomputable def base (v : V) : Step R 0 1 where
  previous := 0
  current := cone v
  equation c hc := by
    have he : boundary c=0 := by
      have hz : ∀l,List.Pairwise R l → l.length=0 → boundary (single l 1)=(0 : Chain V) := by
        intro l hl hn
        have : l=[] := List.length_eq_zero_iff.mp hn
        simp [this,faceSum]
      exact linear_eq_on_admissible boundary 0 hz hc
    simp [boundary_cone,he]
  admissible l hl hn := by
    have : l=[] := List.length_eq_zero_iff.mp hn
    simp only [this,cone_single]
    exact admissible_single (by simp) (by simp) _
  bounded l hl hn := by
    have : l=[] := List.length_eq_zero_iff.mp hn
    simp only [this,cone_single]
    exact (Finset.card_le_card (vertices_single_subset [v] (1:ℤ))).trans (by simp)

noncomputable def residual (l : List V) : Chain V := single l 1-D.current (faceSum l)

theorem residual_admissible {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    Admissible R (n+1) (D.residual l) := by
  apply admissible_sub (admissible_single hl hn 1)
  exact admissible_linear D.current (admissible_faceSum hl hn) D.admissible

theorem residual_cycle {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    boundary (D.residual l)=0 := by
  have he := D.equation (faceSum l) (admissible_faceSum hl hn)
  simp only [boundary_faceSum,map_zero,add_zero] at he
  simp [residual,he]

theorem residual_bound {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    (vertices (D.residual l)).card≤(n+1)+(n+1)*b := by
  have hb : (vertices (D.current (faceSum l))).card≤(n+1)*b := by
    apply (vertices_linear_card D.current (faceSum l) b ?_).trans
      (Nat.mul_le_mul_right b ((faceSum_support_card l).trans hn.le))
    intro s hs
    have had := admissible_faceSum hl hn s hs
    exact D.bounded s had.1 had.2
  calc
    _ ≤ (vertices (single l 1)∪vertices (D.current (faceSum l))).card :=
      Finset.card_le_card (vertices_sub_subset _ _)
    _ ≤ (vertices (single l 1)).card+(vertices (D.current (faceSum l))).card := Finset.card_union_le _ _
    _ ≤ l.toFinset.card+(n+1)*b := Nat.add_le_add
      (Finset.card_le_card (vertices_single_subset _ _)) hb
    _ ≤ (n+1)+(n+1)*b := Nat.add_le_add_right ((List.toFinset_card_le l).trans hn.le) _

variable (hc : ∀S : Finset V,S.card≤(n+1)+(n+1)*b → ∃v,∀w∈S,R v w)

noncomputable def nextVertex (l : List V) (hl : List.Pairwise R l ∧ l.length=n+1) : V :=
  (hc (vertices (D.residual l)) (D.residual_bound hl.1 hl.2)).choose

theorem nextVertex_rel (l : List V) (hl : List.Pairwise R l ∧ l.length=n+1) :
    ∀w∈vertices (D.residual l),R (D.nextVertex hc l hl) w :=
  (hc _ (D.residual_bound hl.1 hl.2)).choose_spec

noncomputable def nextGenerator (l : List V) : Chain V :=
  if hl : List.Pairwise R l ∧ l.length=n+1 then
    cone (D.nextVertex hc l hl) (D.residual l) else 0

noncomputable def next : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.linearCombination ℤ (D.nextGenerator hc)

@[simp] theorem next_single (l : List V) :
    D.next hc (single l 1)=D.nextGenerator hc l := by simp [next]

theorem next_contraction {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    boundary (D.next hc (single l 1))+D.current (boundary (single l 1))=single l 1 := by
  rw [next_single,nextGenerator,dite_eq_left ⟨hl,hn⟩,boundary_cone,D.residual_cycle hl hn]
  simp [residual]

theorem next_admissible {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    Admissible R (n+1+1) (D.next hc (single l 1)) := by
  rw [next_single,nextGenerator,dite_eq_left ⟨hl,hn⟩]
  exact admissible_cone (D.residual_admissible hl hn) _ (D.nextVertex_rel hc l ⟨hl,hn⟩)

theorem next_bounded {l : List V} (hl : List.Pairwise R l) (hn : l.length=n+1) :
    (vertices (D.next hc (single l 1))).card≤1+(n+1)+(n+1)*b := by
  rw [next_single,nextGenerator,dite_eq_left ⟨hl,hn⟩]
  have hi := Finset.card_le_card (vertices_cone_subset (D.nextVertex hc l ⟨hl,hn⟩) (D.residual l))
  have hj := Finset.card_insert_le (D.nextVertex hc l ⟨hl,hn⟩) (vertices (D.residual l))
  have hb := D.residual_bound hl hn
  omega

noncomputable def extend : Step R (n+1) (1+(n+1)+(n+1)*b) where
  previous := D.current
  current := D.next hc
  equation c h := by
    have he : (boundary.comp (D.next hc)+D.current.comp boundary) c=LinearMap.id c :=
      linear_eq_on_admissible _ _ (fun _ hl hn => D.next_contraction hc hl hn) h
    exact he
  admissible _ := D.next_admissible hc
  bounded _ := D.next_bounded hc

include D in

theorem fills {c : Chain V} (hc : Admissible R n c) (hz : boundary c=0) :
    ∃d,Admissible R (n+1) d ∧ boundary d=c := by
  refine ⟨D.current c,admissible_linear D.current hc D.admissible,?_⟩
  have he := D.equation c hc
  simpa [hz] using he

end Step

def bankBound : ℕ → ℕ
  | 0 => 1
  | n+1 => 1+(n+1)+(n+1)*bankBound n

theorem bankBound_mono : Monotone bankBound := by
  apply monotone_nat_of_le_succ
  intro n
  rw [bankBound]
  have hh : bankBound n≤(n+1)*bankBound n := by nlinarith
  omega

theorem exists_step (N : ℕ)
    (hc : ∀S : Finset V,S.card≤bankBound N → ∃v,∀w∈S,R v w) :
    ∀n≤N,Nonempty (Step R n (bankBound n)) := by
  intro n hn
  induction n with
  | zero =>
    obtain ⟨v,hv⟩ := hc ∅ (by simp)
    exact ⟨Step.base v⟩
  | succ n ih =>
    obtain ⟨D⟩ := ih (by omega)
    refine ⟨D.extend (fun S hS => hc S ?_)⟩
    apply hS.trans
    apply le_trans (by simp only [bankBound]; omega) (bankBound_mono hn)

theorem low_degree_filling
    (hc : ∀S : Finset V,S.card≤31 → ∃v,∀w∈S,R v w)
    {n : ℕ} (hn : n≤3) {c : Chain V} (had : Admissible R n c) (hz : boundary c=0) :
    ∃d,Admissible R (n+1) d ∧ boundary d=c := by
  obtain ⟨D⟩ := exists_step (R:=R) 3 (by simpa [bankBound] using hc) n hn
  exact D.fills had hz

end ConfigurationChains
end BoundedConfigurationContraction

end SimpleAmenable
end
end

end OAI
