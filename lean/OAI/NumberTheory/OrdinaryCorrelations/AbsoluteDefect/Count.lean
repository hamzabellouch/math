import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryCofactorWeight
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def count (ω : ι → Bool) : ℕ := (Finset.univ.filter (fun i => ω i=true)).card

omit [DecidableEq ι] in
lemma pow_count (ω : ι → Bool) (z : ℝ) :
    z^count ω=∏i,if ω i=true then z else 1 := by
  rw [Finset.prod_ite]
  simp [count]

lemma power_count_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ω : ι → Bool) (z : ℝ) :
    z^count ω=∑t∈(univ : Finset ι).powerset,
      (z-1)^t.card*(if ∀i∈t,ω i=true then (1:ℝ) else 0) := by
  rw [pow_count]
  have he : (∏i,if ω i=true then z else 1)=
      ∏i,((z-1)*(if ω i=true then (1:ℝ) else 0)+1) := by
    apply prod_congr rfl
    intro i _
    split_ifs <;> ring
  rw [he,prod_add_one]
  apply sum_congr rfl
  intro t ht
  rw [prod_mul_distrib,prod_const,prod_boole]
  by_cases h : ∀i∈t,ω i=true <;> simp [h]

lemma polynomial_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (z : ℝ) :
    (∏i,(1-(1-z)*v i))=∑t∈(univ : Finset ι).powerset,
      (z-1)^t.card*∏i∈t,v i := by
  have he : (∏i,(1-(1-z)*v i))=∏i,((z-1)*v i+1) := by
    apply prod_congr rfl
    intro i _
    ring
  rw [he,prod_add_one]
  apply sum_congr rfl
  intro t ht
  rw [prod_mul_distrib,prod_const]

def primeBits (P : Finset ℕ) (n : ℕ) : ↥P → Bool := fun p => decide ((p:ℕ)∣n)

def arithmeticGenerating (P : Finset ℕ) (N : ℕ) (z : ℝ) : ℝ :=
  ∑n∈Finset.Icc 1 N,(N:ℝ)⁻¹*z^count (primeBits P n)

lemma selected_prod_dvd_iff (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (t : Finset ↥P) (n : ℕ) :
    (∏p∈t,(p:ℕ))∣n ↔ ∀p∈t,(p:ℕ)∣n := by
  constructor
  · intro hn p hp
    exact dvd_trans (dvd_prod_of_mem (fun p : ↥P => (p:ℕ)) hp) hn
  · induction t using Finset.induction_on with
    | empty => simp
    | @insert p t hpt ih =>
      intro hn
      rw [prod_insert hpt]
      have hc : (p:ℕ).Coprime (∏q∈t,(q:ℕ)) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
        intro he
        exact hpt ((Subtype.ext he : p=q).symm ▸ hq)
      exact hc.mul_dvd_of_dvd_of_dvd (hn p (mem_insert_self p t))
        (ih (fun q hq => hn q (mem_insert_of_mem hq)))

lemma sum_multiples_Ioc (v u p : ℕ) (hp : 0<p) (g : ℕ → ℝ) :
    (∑n∈(Finset.Ioc v u).filter (fun n => p∣n),g n)=
      ∑m∈Finset.Ioc (v/p) (u/p),g (p*m) := by
  symm
  refine sum_bij (fun m _ => p*m) ?_ ?_ ?_ ?_
  · intro m hm
    rcases mem_Ioc.mp hm with ⟨hl,hu⟩
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨?_,?_⟩,dvd_mul_right p m⟩
    · simpa only [mul_comm] using (Nat.div_lt_iff_lt_mul hp).mp hl
    · simpa only [mul_comm] using (Nat.le_div_iff_mul_le hp).mp hu
  · intro m hm m' hm' he
    exact Nat.eq_of_mul_eq_mul_left hp he
  · intro n hn
    rcases mem_filter.mp hn with ⟨hn,hpn⟩
    have he := Nat.mul_div_cancel' hpn
    refine ⟨n/p,mem_Ioc.mpr ⟨?_,?_⟩,he⟩
    · apply (Nat.div_lt_iff_lt_mul hp).mpr
      simpa only [mul_comm (n/p),he] using (mem_Ioc.mp hn).1
    · apply (Nat.le_div_iff_mul_le hp).mpr
      simpa only [mul_comm (n/p),he] using (mem_Ioc.mp hn).2
  · intro m hm
    rfl

lemma card_multiples_Icc (N q : ℕ) (hq : 0<q) :
    ((Finset.Icc 1 N).filter (fun n => q∣n)).card=N/q := by
  have h := sum_multiples_Ioc 0 N q hq (fun _ => (1:ℝ))
  have he (a : ℕ) : Finset.Ioc 0 a=Finset.Icc 1 a := by ext n; simp only [Finset.mem_Ioc,Finset.mem_Icc]; omega
  have hh : (((Finset.Icc 1 N).filter (fun n => q∣n)).card:ℝ)=(N/q:ℕ) := by
    simpa only [he,sum_const,nsmul_eq_mul,mul_one,
      Nat.zero_div,Nat.card_Icc,Nat.add_sub_cancel] using h
  exact_mod_cast hh

lemma prime_joint_mass (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (N : ℕ) (t : Finset ↥P) :
    (∑n∈Finset.Icc 1 N,(N:ℝ)⁻¹*(if ∀p∈t,primeBits P n p=true then (1:ℝ) else 0))=
      ((N/(∏p∈t,(p:ℕ)):ℕ):ℝ)/N := by
  have hq : 0<∏p∈t,(p:ℕ) := prod_pos (fun p _ => (hP p p.property).pos)
  simp only [primeBits,decide_eq_true_eq,←selected_prod_dvd_iff P hP t]
  rw [←mul_sum]
  have hs : (∑n∈Finset.Icc 1 N,if (∏p∈t,(p:ℕ))∣n then (1:ℝ) else 0)=
      ((N/(∏p∈t,(p:ℕ)):ℕ):ℝ) := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one,card_multiples_Icc N _ hq]
  rw [hs]
  ring

lemma arithmetic_expansion (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (N : ℕ) (z : ℝ) :
    arithmeticGenerating P N z=∑t∈(univ : Finset ↥P).powerset,
      (z-1)^t.card*(((N/(∏p∈t,(p:ℕ)):ℕ):ℝ)/N) := by
  unfold arithmeticGenerating
  simp_rw [power_count_expansion,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  rw [←prime_joint_mass P hP N t,mul_sum]
  apply sum_congr rfl
  intro n hn
  ring

lemma count_primeBits (P : Finset ℕ) (n : ℕ) :
    count (primeBits P n)=(P.filter (fun p => p∣n)).card := by
  unfold count primeBits
  apply card_bij (fun (p : ↥P) _ => (p:ℕ))
  · intro p hp
    exact mem_filter.mpr ⟨p.property, by simpa using (Finset.mem_filter.mp hp).2⟩
  · intro p hp q hq he
    exact Subtype.ext he
  · intro p hp
    refine ⟨⟨p,(mem_filter.mp hp).1⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using (mem_filter.mp hp).2⟩

end OrdinaryCofactorWeight

end

end OAI
