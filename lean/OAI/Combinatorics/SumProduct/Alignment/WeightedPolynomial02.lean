import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.FilteredShears01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
open scoped commutatorElement

 
end

section
 

noncomputable section
open scoped BigOperators
namespace WeightedPolynomial
open MvPolynomial
open FilteredShears.PolynomialShears
variable {σ τ : Type*} {w : σ → ℕ} {d e : ℕ}

lemma bounded_iff_degreeLT (p : MvPolynomial σ ℝ) :
    Bounded w d p ↔ p∈degreeLT w (d+1) := by
  constructor <;> intro h m hm
  · exact Nat.lt_succ_iff.mpr (h m hm)
  · exact Nat.lt_succ_iff.mp (h m hm)
lemma Bounded.mono {p : MvPolynomial σ ℝ} (hp : Bounded w d p) (h : d ≤ e) :
    Bounded w e p := fun m hm=>le_trans (hp m hm) h
lemma bounded_zero : Bounded w d (0 : MvPolynomial σ ℝ) := by intro m hm; simp at hm
lemma bounded_C (a : ℝ) : Bounded w d (C a) :=
  ((bounded_iff_degreeLT _).mpr (C_mem w a)).mono (Nat.zero_le _)
lemma bounded_X (i : σ) : Bounded w (w i) (X (R:=ℝ) i) :=
  (bounded_iff_degreeLT _).mpr (X_mem w i)
lemma Bounded.add {p q : MvPolynomial σ ℝ} (hp : Bounded w d p) (hq : Bounded w d q) :
    Bounded w d (p+q) :=
  (bounded_iff_degreeLT _).mpr ((degreeLT w (d+1)).add_mem
    ((bounded_iff_degreeLT _).mp hp) ((bounded_iff_degreeLT _).mp hq))
lemma Bounded.neg {p : MvPolynomial σ ℝ} (hp : Bounded w d p) : Bounded w d (-p) :=
  (bounded_iff_degreeLT _).mpr ((degreeLT w (d+1)).neg_mem ((bounded_iff_degreeLT _).mp hp))
lemma Bounded.sub {p q : MvPolynomial σ ℝ} (hp : Bounded w d p) (hq : Bounded w d q) :
    Bounded w d (p-q) := by simpa only [sub_eq_add_neg] using hp.add hq.neg
lemma Bounded.mul {p q : MvPolynomial σ ℝ} (hp : Bounded w d p) (hq : Bounded w e q) :
    Bounded w (d+e) (p*q) := by
  apply (bounded_iff_degreeLT _).mpr
  simpa only [Nat.add_right_comm] using (mul_mem (w:=w) (a:=d+1) (b:=e)
    ((bounded_iff_degreeLT p).mp hp) ((bounded_iff_degreeLT q).mp hq))
lemma Bounded.pow {p : MvPolynomial σ ℝ} (hp : Bounded w d p) (k : ℕ) :
    Bounded w (d*k) (p^k) := by
  induction k with
  | zero => simpa using bounded_C (w:=w) (d:=0) 1
  | succ k ih => simpa [pow_succ,Nat.mul_succ] using ih.mul hp
lemma bounded_sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℝ)
    (hp : ∀ i∈s,Bounded w d (p i)) : Bounded w d (∑ i∈s,p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (bounded_zero (w:=w) (d:=d))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).add (ih (fun j hj=>hp j (Finset.mem_insert_of_mem hj)))
lemma bounded_prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℝ) (a : ι → ℕ)
    (hp : ∀ i∈s,Bounded w (a i) (p i)) : Bounded w (∑ i∈s,a i) (∏ i∈s,p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_C (w:=w) (d:=0) 1
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj=>hp j (Finset.mem_insert_of_mem hj)))

 

lemma Bounded.substitute {v : τ → ℕ} {p : MvPolynomial τ ℝ}
    (hp : Bounded v d p) (q : τ → MvPolynomial σ ℝ)
    (hq : ∀ i,Bounded w (v i) (q i)) :
    Bounded w d (eval₂Hom C q p) := by
  classical
  conv => arg 3; rw [p.as_sum]
  rw [map_sum]
  apply bounded_sum
  intro m hm
  change Bounded w d (eval₂ C q (monomial m (p.coeff m)))
  rw [eval₂_monomial]
  have hprod:=bounded_prod m.support (fun i=>(q i)^(m i)) (fun i=>v i*m i)
    (fun i _=>(hq i).pow (m i))
  have he : (∑ i∈m.support,v i*m i)=Finsupp.weight v m := by
    simp only [Finsupp.weight_apply,Finsupp.sum,smul_eq_mul,Nat.mul_comm]
  rw [he] at hprod
  exact ((bounded_C (w:=w) (d:=0) (p.coeff m)).mul hprod).mono
    (by simpa using hp m (mem_support_iff.mp hm))

end WeightedPolynomial
end
 
end

section
 

noncomputable section
namespace WeightedPolynomial
open MvPolynomial
variable {σ τ : Type*}
def IsWeighted (w : σ → ℕ) (d : ℕ) (f : (σ → ℝ) → ℝ) : Prop :=
  ∃ p : MvPolynomial σ ℝ,Bounded w d p ∧ ∀ x,f x=eval x p
lemma IsWeighted.const (w : σ → ℕ) (d : ℕ) (a : ℝ) : IsWeighted w d (fun _=>a) :=
  ⟨C a,bounded_C a,by simp⟩
lemma IsWeighted.coordinate (w : σ → ℕ) (i : σ) : IsWeighted w (w i) (fun x=>x i) :=
  ⟨X i,bounded_X i,by simp⟩
lemma IsWeighted.mono {w : σ → ℕ} {d e : ℕ} {f : (σ → ℝ) → ℝ}
    (hf : IsWeighted w d f) (h : d ≤ e) : IsWeighted w e f := by
  obtain ⟨p,hp,hf⟩:=hf
  exact ⟨p,hp.mono h,hf⟩
lemma IsWeighted.add {w : σ → ℕ} {d : ℕ} {f g : (σ → ℝ) → ℝ}
    (hf : IsWeighted w d f) (hg : IsWeighted w d g) : IsWeighted w d (fun x=>f x+g x) := by
  obtain ⟨p,hp,hf⟩:=hf
  obtain ⟨q,hq,hg⟩:=hg
  exact ⟨p+q,hp.add hq,by simp [hf,hg]⟩
lemma IsWeighted.sub {w : σ → ℕ} {d : ℕ} {f g : (σ → ℝ) → ℝ}
    (hf : IsWeighted w d f) (hg : IsWeighted w d g) : IsWeighted w d (fun x=>f x-g x) := by
  obtain ⟨p,hp,hf⟩:=hf
  obtain ⟨q,hq,hg⟩:=hg
  exact ⟨p-q,hp.sub hq,by simp [hf,hg]⟩
lemma IsWeighted.comp {w : σ → ℕ} {v : τ → ℕ} {d : ℕ} {f : (τ → ℝ) → ℝ}
    (hf : IsWeighted v d f) {g : (σ → ℝ) → (τ → ℝ)}
    (hg : ∀ i,IsWeighted w (v i) (fun x=>g x i)) :
    IsWeighted w d (fun x=>f (g x)) := by
  obtain ⟨p,hp,hf⟩:=hf
  choose q hq he using hg
  refine ⟨eval₂Hom C q p,hp.substitute q hq,?_⟩
  intro x
  change f (g x)=eval x (eval₂ C q p)
  rw [hf,← eval_assoc]
  exact congrArg (fun a=>eval a p) (funext (fun i=>he i x))
end WeightedPolynomial

namespace RationalLattice
open WeightedPolynomial MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (H : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)

include hsk hH in
omit [IsTopologicalGroup G] in
lemma logCorrection_weighted (i : Fin n) :
    IsWeighted (fun j : Fin i.val=>w ⟨j.val,lt_trans j.isLt i.isLt⟩) (w i)
      (fun x=>MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (logCorrection c i)) := by
  have hg (j : Fin n) : IsWeighted (fun j : Fin i.val=>w ⟨j.val,lt_trans j.isLt i.isLt⟩) (w j)
      (fun x=>prefixSection i x j) := by
    unfold prefixSection
    by_cases hj : j < i
    · simp only [dite_eq_left hj]
      exact IsWeighted.coordinate (fun k : Fin i.val=>w ⟨k.val,lt_trans k.isLt i.isLt⟩) ⟨j.val,hj⟩
    · simp only [dite_eq_right hj]
      exact IsWeighted.const _ _ 0
  have hh:=IsWeighted.comp (canonicalLog_weighted c hsk H w hH i) hg
  simpa only [logCorrection_eval] using hh

include hsk hH in
 

omit [IsTopologicalGroup G] in
theorem canonicalExp_weighted (i : Fin n) :
    IsWeighted w (w i) (fun x=>c.coord (canonicalExp c x) i) := by
  have aux : ∀ k,∀ hk : k<n,IsWeighted w (w ⟨k,hk⟩)
      (fun x=>c.coord (canonicalExp c x) ⟨k,hk⟩) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      let i : Fin n:=⟨k,hk⟩
      have hp:=IsWeighted.sub (IsWeighted.coordinate w i)
        ((logCorrection_weighted c hsk H w hH i).comp
          (fun j : Fin k=>ih j.val j.isLt (lt_trans j.isLt hk)))
      have he (x : Fin n → ℝ) :
          c.coord (canonicalExp c x) i=x i-MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (fun j : Fin k=>c.coord (canonicalExp c x) ⟨j.val,lt_trans j.isLt hk⟩)
            (logCorrection c i) := by
        have hh:=congrFun (canonicalLog_eq_forward c (canonicalExp c x)) i
        rw [canonicalLog_exp] at hh
        change x i=c.coord (canonicalExp c x) i+_ at hh
        linarith
      obtain ⟨p,hp,hq⟩:=hp
      refine ⟨p,hp,?_⟩
      intro x
      exact (he x).trans (hq x)
  exact aux i.val i.isLt

end RationalLattice
end
 
end

section
 

noncomputable section
open scoped BigOperators
namespace WeightedPolynomial
open MvPolynomial
variable {α β : Type*}

lemma eval_kill_inr (p : MvPolynomial (α ⊕ β) ℝ) (y : β → ℝ) :
    eval y (p.killCompl Sum.inr_injective)=eval (Sum.elim (fun _ : α=>0) y) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    cases i with
    | inl i => simp [map_mul,killCompl]
    | inr i =>
      have he : killCompl (R:=ℝ) (Sum.inr_injective (α:=α)) (X (Sum.inr i))=X i := by
        rw [← rename_X,killCompl_rename_app]
      simp [map_mul,hp,he]

lemma exists_left_of_vanishing (p : MvPolynomial (α ⊕ β) ℝ)
    (hz : ∀ y,eval (Sum.elim (fun _ : α=>0) y) p=0)
    (m : (α ⊕ β) →₀ ℕ) (hm : p.coeff m≠0) : ∃ a : α,m (Sum.inl a)≠0 := by
  classical
  by_contra hh
  push Not at hh
  have hs : ↑m.support ⊆ Set.range (@Sum.inr α β) := by
    intro j hj
    cases j with
    | inl a => exact False.elim ((Finsupp.mem_support_iff.mp hj) (hh a))
    | inr b => exact ⟨b,rfl⟩
  have hk : p.killCompl Sum.inr_injective=0 := by
    apply MvPolynomial.funext
    intro y
    rw [map_zero,eval_kill_inr,hz]
  have hc:=congrArg (fun poly : MvPolynomial β ℝ=>
    poly.coeff (m.comapDomain (@Sum.inr α β) Sum.inr_injective.injOn)) hk
  rw [coeff_killCompl,m.mapDomain_comapDomain _ Sum.inr_injective hs,
    AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at hc
  exact hm hc

 

theorem fixed_left_spends_weight (wa : α → ℕ) (wb : β → ℕ)
    (hwa : ∀ a,0 < wa a) {d : ℕ} (p : MvPolynomial (α ⊕ β) ℝ)
    (hp : Bounded (Sum.elim wa wb) d p)
    (hz : ∀ y,eval (Sum.elim (fun _ : α=>0) y) p=0) (a : α → ℝ) :
    Bounded wb (d-1) (eval₂Hom C (Sum.elim (fun i=>C (a i)) (fun j=>X j)) p) := by
  have hbound : Bounded (Sum.elim (fun _ : α=>0) wb) (d-1) p := by
    intro m hm
    obtain ⟨i,hi⟩:=exists_left_of_vanishing p hz m hm
    have hlt : Finsupp.weight (Sum.elim (fun _ : α=>0) wb) m < Finsupp.weight (Sum.elim wa wb) m := by
      classical
      simp only [Finsupp.weight_apply,Finsupp.sum,smul_eq_mul]
      apply Finset.sum_lt_sum
      · intro j hj
        apply Nat.mul_le_mul_left
        cases j <;> simp
      · refine ⟨Sum.inl i,Finsupp.mem_support_iff.mpr hi,?_⟩
        simpa using Nat.mul_pos (Nat.pos_of_ne_zero hi) (hwa i)
    have hle:=hp m hm
    omega
  apply hbound.substitute
  intro i
  cases i with
  | inl i => exact bounded_C (d:=0) _
  | inr j => exact bounded_X j

end WeightedPolynomial

end
end
end

end OAI
