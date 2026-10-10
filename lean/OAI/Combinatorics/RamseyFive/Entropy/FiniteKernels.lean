import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BlockReveal

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def sigmaLaw {A : Type*} [Fintype A] {B : A→Type*} [∀ a,Fintype (B a)]
    (p : Law A) (q : ∀ a,Law (B a)) : Law (Sigma B) where
  mass z := p z.1*q z.1 z.2
  nonneg z := mul_nonneg (p.nonneg _) ((q z.1).nonneg _)
  sum_one := by rw [Fintype.sum_sigma]; simp only [←Finset.mul_sum,(q _).sum_one,mul_one,p.sum_one]

lemma mean_sigma {A : Type*} [Fintype A] {B : A→Type*} [∀ a,Fintype (B a)]
    (p : Law A) (q : ∀ a,Law (B a)) (f : Sigma B→ℝ) :
    mean (sigmaLaw p q) f=mean p (fun a=>mean (q a) (fun b=>f ⟨a,b⟩)) := by
  simp only [mean,sigmaLaw,Fintype.sum_sigma,Finset.mul_sum,mul_assoc]

lemma map_adaptive_first (p : Law α) (q : α→Law β) :
    map (adaptiveLaw p q) Prod.fst=p := by
  apply Law.ext
  funext a
  simp only [map,adaptiveLaw,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel,←Finset.mul_sum,(q _).sum_one,mul_one]
  simp

lemma second_adaptive (p : Law α) (q : α→Law β) (b : β) :
    second (adaptiveLaw p q) b=∑ a,p a*q a b := rfl

lemma fiber_adaptive (p : Law α) (q : α→Law β) (a : α) (ha : 0<p a) :
    fiber (adaptiveLaw p q) a=q a := by
  have hf : first (adaptiveLaw p q)=p := by
    apply Law.ext
    funext a
    simp only [first,adaptiveLaw,←Finset.mul_sum,(q a).sum_one,mul_one]
  apply Law.ext
  funext b
  have hh:=mass_eq_first_mul_fiber (adaptiveLaw p q) a b
  rw [hf] at hh
  change p a*q a b=p a*fiber (adaptiveLaw p q) a b at hh
  exact (mul_left_cancel₀ ha.ne' hh).symm

lemma adaptive_stream (p : Law α) (q : α→Law β) (s : α→γ) :
    map (adaptiveLaw p q) (fun z=>s z.1)=map p s := by
  change map (adaptiveLaw p q) (s ∘ Prod.fst)=map p s
  rw [←map_comp,map_adaptive_first]

lemma Law.ext_mean (p q : Law α) (h : ∀ f,mean p f=mean q f) : p=q := by
  apply Law.ext
  funext a
  have hh:=h (fun b=>if b=a then 1 else 0)
  simpa only [mean,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh

lemma adaptive_reconstruct (q : Law (α×β)) :
    adaptiveLaw (first q) (fiber q)=q := by
  apply Law.ext
  funext z
  exact (mass_eq_first_mul_fiber q z.1 z.2).symm

lemma map_adaptive_source (p : Law α) (x : α→β) (q : β→Law γ) :
    map (adaptiveLaw p (fun a=>q (x a))) (fun z=>(x z.1,z.2))=
      adaptiveLaw (map p x) q := by
  apply Law.ext_mean
  intro f
  rw [mean_map,mean_adaptive,mean_adaptive,mean_map]

def liftObserved (p : Law α) (x : α→β) (q : Law (β×γ)) : Law (α×γ) :=
  adaptiveLaw p (fun a=>fiber q (x a))

lemma liftObserved_original (p : Law α) (x : α→β) (q : Law (β×γ)) :
    map (liftObserved p x q) Prod.fst=p := map_adaptive_first _ _

lemma liftObserved_joint (p : Law α) (x : α→β) (q : Law (β×γ))
    (hq : first q=map p x) :
    map (liftObserved p x q) (fun z=>(x z.1,z.2))=q := by
  rw [liftObserved,map_adaptive_source,←hq,adaptive_reconstruct]

lemma liftObserved_stream (p : Law α) (x : α→β) (q : Law (β×γ))
    {υ : Type*} [Fintype υ] (s : α→υ) :
    map (liftObserved p x q) (fun z=>s z.1)=map p s := adaptive_stream _ _ _

end

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
local instance blockHistIndexDecEq : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance blockHistSubtypeDecEq (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _

def BlockHistory (B A T β : Type) [Fintype B] [Fintype A] [Fintype T] : ℕ→Type
  | 0 => Unit
  | n+1 => Σ s : B→A, (representativeSet (T:=T) s→β)×BlockHistory B A T β n

instance blockHistoryFintype : (n : ℕ)→Fintype (BlockHistory B A T β n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
    letI := blockHistoryFintype n
    exact inferInstanceAs (Fintype (Σ s : B→A,
      (representativeSet (T:=T) s→β)×BlockHistory B A T β n))

def historyPosterior (p : Law (((B×A)⊕T)→β)) :
    {n : ℕ}→BlockHistory B A T β n→Law (((B×A)⊕T)→β)
  | 0,_ => p
  | _n+1,h => historyPosterior (fiber (reveal p (representativeSet h.1)) h.2.1) h.2.2

def historyUnused (S : B→Finset A) : {n : ℕ}→BlockHistory B A T β n→B→Finset A
  | 0,_ => S
  | _n+1,h => historyUnused (eraseBlock S h.1) h.2.2

def historyLaw (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) :
    (n : ℕ)→Law (BlockHistory B A T β n)
  | 0 => uniformType Unit
  | n+1 => sigmaLaw (freshBlockLaw S) fun s=>
      adaptiveLaw (first (reveal p (representativeSet s))) fun a=>
        historyLaw (fiber (reveal p (representativeSet s)) a) (eraseBlock S s) n

theorem history_posterior_mean (p : Law (((B×A)⊕T)→β)) (S : B→Finset A)
    (n : ℕ) (x : ((B×A)⊕T)→β) :
    mean (historyLaw p S n) (fun h=>historyPosterior p h x)=p x := by
  induction n generalizing p S with
  | zero =>
    change mean (uniformType Unit) (fun _ => p x) = p x
    exact mean_const _ _
  | succ n ih =>
    change mean (sigmaLaw (freshBlockLaw S) fun s=>
      adaptiveLaw (first (reveal p (representativeSet s))) fun a=>
        historyLaw (fiber (reveal p (representativeSet s)) a) (eraseBlock S s) n)
      (fun h=>historyPosterior (fiber (reveal p (representativeSet h.1)) h.2.1) h.2.2 x)=p x
    rw [mean_sigma]
    have hpoint (s : B→A) : mean (adaptiveLaw (first (reveal p (representativeSet s))) fun a=>
        historyLaw (fiber (reveal p (representativeSet s)) a) (eraseBlock S s) n)
        (fun z=>historyPosterior (fiber (reveal p (representativeSet s)) z.1) z.2 x)=p x := by
      rw [mean_adaptive]
      simp_rw [ih]
      change (∑ a,first (reveal p (representativeSet s)) a*
        fiber (reveal p (representativeSet s)) a x)=p x
      simp_rw [←mass_eq_first_mul_fiber]
      exact congrArg (fun r : Law (((B×A)⊕T)→β)=>r x) (second_reveal p _)
    simp_rw [hpoint]
    exact mean_const _ _

def historyTupleLaw (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (n : ℕ) :
    Law (BlockHistory B A T β n×(((B×A)⊕T)→β)) :=
  adaptiveLaw (historyLaw p S n) (historyPosterior p)

lemma historyTuple_second (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (n : ℕ) :
    second (historyTupleLaw p S n)=p := by
  apply Law.ext
  funext x
  exact history_posterior_mean p S n x

lemma historyTuple_fiber (p : Law (((B×A)⊕T)→β)) (S : B→Finset A)
    (n : ℕ) (h : BlockHistory B A T β n) (hh : 0<historyLaw p S n h) :
    fiber (historyTupleLaw p S n) h=historyPosterior p h :=
  fiber_adaptive _ _ _ hh

theorem history_round_mean
    (J : Law (((B×A)⊕T)→β)→(B→Finset A)→(B→A)→ℝ)
    (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (n : ℕ) :
    blockRoundMean J p S (n+1) (Fin.last n)=
      mean (historyLaw p S n) (fun h=>mean (freshBlockLaw (historyUnused S h))
        (J (historyPosterior p h) (historyUnused S h))) := by
  induction n generalizing p S with
  | zero =>
    change mean (freshBlockLaw S) (J p S)=mean (uniformType Unit) (fun _=>mean (freshBlockLaw S) (J p S))
    exact (mean_const _ _).symm
  | succ n ih =>
    change mean (freshBlockLaw S) (fun s=>mean (first (reveal p (representativeSet s)))
      (fun a=>blockRoundMean J (fiber (reveal p (representativeSet s)) a)
        (eraseBlock S s) (n+1) (Fin.last n)))=_
    simp_rw [ih]
    change _=mean (sigmaLaw (freshBlockLaw S) fun s=>
      adaptiveLaw (first (reveal p (representativeSet s))) fun a=>
        historyLaw (fiber (reveal p (representativeSet s)) a) (eraseBlock S s) n)
      (fun h => mean (freshBlockLaw (historyUnused (eraseBlock S h.1) h.2.2))
        (J (historyPosterior (fiber (reveal p (representativeSet h.1)) h.2.1) h.2.2)
          (historyUnused (eraseBlock S h.1) h.2.2)))
    rw [mean_sigma]
    apply mean_congr
    intro s
    rw [mean_adaptive]

lemma blockRoundMean_total_irrel
    (J : Law (((B×A)⊕T)→β)→(B→Finset A)→(B→A)→ℝ)
    (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (n m : ℕ)
    (i : Fin n) (j : Fin m) (hij : i.val=j.val) :
    blockRoundMean J p S n i=blockRoundMean J p S m j := by
  induction n generalizing p S m with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases m with
    | zero => exact Fin.elim0 j
    | succ m =>
      cases i using Fin.cases with
      | zero =>
        have hj : j=0 := Fin.ext (by simpa using hij.symm)
        subst j
        rfl
      | succ i =>
        have hj : j≠0 := by intro hz;subst j;simp at hij
        obtain ⟨j,rfl⟩:=Fin.exists_succ_eq.mpr hj
        simp only [blockRoundMean,Fin.cases_succ]
        apply mean_congr
        intro s
        apply mean_congr
        intro a
        apply ih _ _ _ i j
        simpa using hij

theorem history_pre_round
    (J : Law (((B×A)⊕T)→β)→(B→Finset A)→(B→A)→ℝ)
    (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (n : ℕ) (i : Fin n) :
    blockRoundMean J p S n i=
      mean (historyLaw p S i.val) (fun h=>mean (freshBlockLaw (historyUnused S h))
        (J (historyPosterior p h) (historyUnused S h))) := by
  rw [blockRoundMean_total_irrel J p S n (i.val+1) i (Fin.last i.val) rfl]
  exact history_round_mean J p S i.val

end SharpRamseyFive.FiniteEntropy

end

end OAI
