import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.Pivot

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

structure Original (n : ℕ) (b : ℝ) where
  A : Finset (Projectivization K V)
  B : Finset (Projectivization K (Module.Dual K V))
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  product : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card

abbrev Banks (b : ℝ) := FirstBank (K:=K) (V:=V) b × SecondBank (K:=K) (V:=V) b

def banksLaw (b : ℝ) : PublicTables.Law (Banks (K:=K) (V:=V) b) where
  mass x := (bankLaw (Nat.card K) (b+log 1000000)).mass x.1 *
    (bankLaw (Nat.card K) (b+log 1000000)).mass x.2
  nonneg x := mul_nonneg ((bankLaw _ _).nonneg x.1) ((bankLaw _ _).nonneg x.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [←mul_sum,PublicTables.Law.total,mul_one]

omit [Finite K] [FiniteDimensional K V] in
lemma banks_integral (b : ℝ) (f : Banks (K:=K) (V:=V) b→ℝ) :
    (∑ x,(banksLaw b).mass x*f x) =
      ∑ z,(bankLaw (Nat.card K) (b+log 1000000)).mass z *
        ∑ w,(bankLaw (Nat.card K) (b+log 1000000)).mass w*f (z,w) := by
  simp only [banksLaw,Fintype.sum_prod_type,mul_assoc,mul_sum]

variable {n : ℕ} {b τ P H : ℝ}

def Original.Ready (s : Original (K:=K) (V:=V) n b) (τ : ℝ)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) : Prop :=
  (9/10:ℝ)*s.A.card≤(s.A∩U.1).card ∧ (9/10:ℝ)*s.B.card≤(s.B∩U.2).card ∧
    (incidenceCount s.A s.B:ℝ)≤τ*(s.A.card:ℝ)*s.B.card/Nat.card K

variable (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

omit [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma Original.sparse (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (hr : s.Ready τ U) (hτsmall : τ≤1/40000) :
    (incidenceCount s.A s.B:ℝ)≤(s.A.card:ℝ)*s.B.card/(40000*Nat.card K) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
  apply hr.2.2.trans
  have h := mul_le_mul_of_nonneg_right hτsmall (show 0≤(s.A.card:ℝ)*s.B.card/Nat.card K by positivity)
  convert h using 1 <;> ring

def Book.prepare (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (hr : s.Ready τ U) :
    Input n s.A s.B b :=
  (book.input hdim s.A s.B U s.nonemptyA s.nonemptyB hτ hr.1 hr.2.1 s.product hr.2.2
    (s.sparse U hr hτsmall)).choose

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma Book.prepare_spec (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (hr : s.Ready τ U) :
    let d := book.prepare hdim hτ hτsmall s U hr
    (d.U,d.UT)=U ∧ d.W∈book.library U (s.A∩U.1).card (s.B∩U.2).card ∧ d.W⊆U.1 := by
  exact (book.input hdim s.A s.B U s.nonemptyA s.nonemptyB hτ hr.1 hr.2.1 s.product hr.2.2
    (s.sparse U hr hτsmall)).choose_spec

def Book.choose (s : Original (K:=K) (V:=V) n b)
    (z : Banks (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :
    Option (Code (K:=K) (V:=V) b) :=
  if hr : s.Ready τ U then (book.prepare hdim hτ hτsmall s U hr).choose hdim z.1 z.2 else none

theorem Book.ready_failure (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (hr : s.Ready τ U) :
    (∑ z,(banksLaw b).mass z*(if book.choose hdim hτ hτsmall s z U=none then 1 else 0)) ≤
      2*exp (-(Nat.card K:ℝ)) := by
  simp only [Book.choose,dite_eq_left hr]
  rw [banks_integral]
  exact (book.prepare hdim hτ hτsmall s U hr).choose_failure_bound hdim

theorem Book.dual_exclusion (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (y : Projectivization K (Module.Dual K V)) :
    (∑ z,(banksLaw b).mass z*(book.choose hdim hτ hτsmall s z U).elim 0
      (fun c=>if y∉(mask b z.1 z.2 U c).2 then 1 else 0)) ≤
      12*(Nat.card K:ℝ)*(∑ x,SupportMixtures.kernel s.A x *
        (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  by_cases hr : s.Ready τ U
  · simp only [Book.choose,dite_eq_left hr]
    rw [banks_integral]
    exact (book.prepare hdim hτ hτsmall s U hr).dual_loss_bound hdim y
  · simp only [Book.choose,dite_eq_right hr,Option.elim_none,mul_zero,sum_const_zero]
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun x _=>mul_nonneg (SupportMixtures.kernel_nonneg _ _) (by split_ifs <;> norm_num))

theorem Book.primal_exclusion (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (x : Projectivization K V) :
    (∑ z,(banksLaw b).mass z*(book.choose hdim hτ hτsmall s z U).elim 0
      (fun c=>if x∉(mask b z.1 z.2 U c).1 then 1 else 0)) ≤
      12*(Nat.card K:ℝ)*(∑ y,SupportMixtures.kernel s.B y *
        (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  by_cases hr : s.Ready τ U
  · simp only [Book.choose,dite_eq_left hr]
    rw [banks_integral]
    exact (book.prepare hdim hτ hτsmall s U hr).primal_loss_bound hdim x
  · simp only [Book.choose,dite_eq_right hr,Option.elim_none,mul_zero,sum_const_zero]
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun y _=>mul_nonneg (SupportMixtures.kernel_nonneg _ _) (by split_ifs <;> norm_num))

theorem Book.choose_caps (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (z : Banks (K:=K) (V:=V) b) (c : Code (K:=K) (V:=V) b)
    (hc : book.choose hdim hτ hτsmall s z U=some c) :
    (9/10:ℝ)*s.A.card≤(s.A∩U.1).card ∧ (9/10:ℝ)*s.B.card≤(s.B∩U.2).card ∧
      (read b z.1 z.2 U c).1⊆U.1 ∧ (read b z.1 z.2 U c).2⊆U.2 ∧
      ((read b z.1 z.2 U c).1.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/s.B.card ∧
      ((read b z.1 z.2 U c).2.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/s.A.card := by
  unfold Book.choose at hc
  split at hc
  · rename_i hr
    let d := book.prepare hdim hτ hτsmall s U hr
    have hdom := (book.prepare_spec hdim hτ hτsmall s U hr).1
    have hcap := d.choose_valid hdim z.1 z.2 c hc
    have hu : d.U=U.1 := congrArg Prod.fst hdom
    have hv : d.UT=U.2 := congrArg Prod.snd hdom
    dsimp only at hcap
    rw [hdom,hu,hv] at hcap
    exact ⟨hr.1,hr.2.1,hcap.1,hcap.2.1,hcap.2.2.1,hcap.2.2.2.1⟩
  · cases hc

end
end SharpLogRamsey.ActualPivot

end

end OAI
