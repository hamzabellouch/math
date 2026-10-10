import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BlockSelected

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T : Type} [Fintype B] [Fintype A] [Fintype T] [Nonempty A]
local instance collisionSamplingDecEq : DecidableEq ((B × A) ⊕ T) := Classical.decEq _

def otherCollision (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (s : B → A) (b : B) (a : A) : ℝ :=
  ∑ d ∈ Finset.univ.erase b,c (Sum.inl (b,a)) (Sum.inl (d,s d))

def middleCollision (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (s : B → A) (t : T) : ℝ := ∑ d,c (Sum.inr t) (Sum.inl (d,s d))

def allCollision (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (S : B → Finset A) (s : B → A) : ℝ :=
  (∑ b,∑ a∈S b,otherCollision c s b a)+∑ t,middleCollision c s t

omit [Fintype A] [Fintype T] [Nonempty A] in
lemma otherCollision_own (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (s : B → A) (b : B) (a i : A) :
    otherCollision c (Function.update s b a) b i=otherCollision c s b i := by
  apply Finset.sum_congr rfl
  intro d hd
  rw [Function.update_of_ne (Finset.mem_erase.mp hd).1]

lemma fresh_row_collision (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (hc : ∀ i j,0≤c i j) (S : B → Finset A) (r : ℕ) (hr : 0<r)
    (hS : ∀ b,r≤(S b).card) (i : ((B × A) ⊕ T)) :
    r * mean (freshBlockLaw S) (fun s => ∑ b,c i (Sum.inl (b,s b))) ≤
      ∑ j∈blockActive S,c i j := by
  have hn : ∀ b,(S b).Nonempty := fun b => Finset.card_pos.mp (hr.trans_le (hS b))
  rw [freshBlockLaw_eq S hn,mean_sum,Finset.mul_sum]
  have hb (b : B) : (r:ℝ)*mean (piLaw fun d => uniformOn (S d) (hn d))
      (fun s => c i (Sum.inl (b,s b))) ≤ ∑ a∈S b,c i (Sum.inl (b,a)) := by
    have he : mean (piLaw fun d => uniformOn (S d) (hn d))
        (fun s => c i (Sum.inl (b,s b))) =
        ((S b).card:ℝ)⁻¹ * ∑ a∈S b,c i (Sum.inl (b,a)) := by
      change (∑ s,piLaw (fun d => uniformOn (S d) (hn d)) s *
        (fun a => c i (Sum.inl (b,a))) (s b)) = _
      rw [piLaw_eval_expectation (fun d => uniformOn (S d) (hn d)) b
        (fun a => c i (Sum.inl (b,a))),uniformOn_expectation]
    have hnn := mean_nonneg (piLaw fun d=>uniformOn (S d) (hn d))
      (fun s=>c i (Sum.inl (b,s b))) (fun s=>hc _ _)
    have hcp : ((S b).card:ℝ)≠0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (hn b))
    calc
      _ ≤ (S b).card*mean (piLaw fun d=>uniformOn (S d) (hn d))
          (fun s=>c i (Sum.inl (b,s b))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hS b) hnn
      _ = _ := by rw [he]; field_simp
  apply (Finset.sum_le_sum fun b _=>hb b).trans
  have he : (∑ j∈blockActive S,c i j)=
      (∑ b,∑ a∈S b,c i (Sum.inl (b,a)))+∑ t,c i (Sum.inr t) := by
    calc
      _ = ∑ j,if j∈blockActive S then c i j else 0 := by
        rw [Finset.sum_ite_mem,Finset.univ_inter]
      _ = _ := by
        rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
        simp only [mem_blockActive_left,mem_blockActive_right,ite_true,
          Finset.sum_ite_mem,Finset.univ_inter]
  rw [he]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun t _=>hc _ _)

theorem fresh_all_collision_bound (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (hc : ∀ i j,0≤c i j) (S : B → Finset A) (r : ℕ) (hr : 0<r)
    (hS : ∀ b,r≤(S b).card) :
    r * mean (freshBlockLaw S) (allCollision c S) ≤
      ∑ i∈blockActive S,∑ j∈blockActive S,c i j := by
  have hpoint (s : B → A) : allCollision c S s ≤
      ∑ i∈blockActive S,∑ b,c i (Sum.inl (b,s b)) := by
    have he : (∑ i∈blockActive S,∑ b,c i (Sum.inl (b,s b)))=
        (∑ b,∑ a∈S b,∑ d,c (Sum.inl (b,a)) (Sum.inl (d,s d)))+
        ∑ t,middleCollision c s t := by
      calc
        _ = ∑ i,if i∈blockActive S then ∑ b,c i (Sum.inl (b,s b)) else 0 := by
          rw [Finset.sum_ite_mem,Finset.univ_inter]
        _ = _ := by
          rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
          simp only [mem_blockActive_left,mem_blockActive_right,ite_true,
            Finset.sum_ite_mem,Finset.univ_inter,middleCollision]
    rw [he]
    change _ + _ ≤ _ + _
    apply add_le_add _ le_rfl
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro a _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun d _ _=>hc _ _)
  calc
    _ ≤ r * mean (freshBlockLaw S)
        (fun s=>∑ i∈blockActive S,∑ b,c i (Sum.inl (b,s b))) :=
      mul_le_mul_of_nonneg_left (mean_mono _ hpoint) (Nat.cast_nonneg _)
    _ = ∑ i∈blockActive S,r * mean (freshBlockLaw S)
        (fun s=>∑ b,c i (Sum.inl (b,s b))) := by rw [mean_finset_sum,Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ => fresh_row_collision c hc S r hr hS i

theorem fresh_selected_collision (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (hc : ∀ i j,0≤c i j) (S : B → Finset A) (r : ℕ) (hr : 0<r)
    (hS : ∀ b,r≤(S b).card) :
    r * mean (freshBlockLaw S) (fun s=>∑ b,otherCollision c s b (s b)) ≤
      mean (freshBlockLaw S) (allCollision c S) := by
  apply (fresh_selected_fraction S r hr hS (otherCollision c)
    (fun s b a=>Finset.sum_nonneg fun d _=>hc _ _) (otherCollision_own c)).trans
  apply mean_mono
  intro s
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun t _=>
    Finset.sum_nonneg fun d _=>hc _ _)
end

open scoped Classical BigOperators

def badIndexIndicator (δ g d e : ℝ) : ℝ := if d<δ ∨ e<g then 1 else 0

lemma badIndexIndicator_nonneg (δ g d e : ℝ) : 0≤badIndexIndicator δ g d e := by
  unfold badIndexIndicator
  split_ifs <;> norm_num

lemma badIndexIndicator_le {δ g d e : ℝ} (hδ : 0≤δ) (hg : 0≤g)
    (hd : 0<d) (he : 0<e) : badIndexIndicator δ g d e≤δ/d+g/e := by
  unfold badIndexIndicator
  split_ifs with h
  · rcases h with h|h
    · have hh : 1≤δ/d := (le_div_iff₀ hd).mpr (by linarith)
      exact hh.trans (le_add_of_nonneg_right (div_nonneg hg he.le))
    · have hh : 1≤g/e := (le_div_iff₀ he).mpr (by linarith)
      exact hh.trans (le_add_of_nonneg_left (div_nonneg hδ hd.le))
  · positivity

lemma badIndexIndicator_eq_zero {δ g d e : ℝ} (h : badIndexIndicator δ g d e=0) :
    δ≤d ∧ g≤e := by
  unfold badIndexIndicator at h
  split_ifs at h with hh
  · norm_num at h
  · push Not at hh
    exact hh

lemma bad_count_bound {I : Type*} [DecidableEq I] (S : Finset I)
    (δ g : I→ℝ) (d e : ℝ) (hδ : ∀ i∈S,0≤δ i) (hg : ∀ i∈S,0≤g i)
    (hd : 0<d) (he : 0<e) :
    ((S.filter (fun i=>d<δ i ∨ e<g i)).card:ℝ)≤
      (∑ i∈S,δ i)/d+(∑ i∈S,g i)/e := by
  have hsum : ((S.filter (fun i=>d<δ i ∨ e<g i)).card:ℝ)=
      ∑ i∈S,badIndexIndicator (δ i) (g i) d e := by
    simp only [badIndexIndicator,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [hsum]
  calc
    _ ≤ ∑ i∈S,(δ i/d+g i/e) := Finset.sum_le_sum fun i hi=>badIndexIndicator_le (hδ i hi) (hg i hi) hd he
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_div,Finset.sum_div]

variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
local instance goodDeleteIndexDecEq : DecidableEq ((B×A)⊕T) := Classical.decEq _

def indexInformation (p : Law (((B×A)⊕T)→β)) (s : B→A) : ((B×A)⊕T)→ℝ :=
  Sum.elim (fun z=>(blockInformation p s z.1 z.2 : ℝ)) (fun t=>(middleInformation p s t : ℝ))

def indexCollision (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (s : B→A) : ((B×A)⊕T)→ℝ :=
  Sum.elim (fun z=>otherCollision c s z.1 z.2) (middleCollision c s)

def indexBad (J d e : ℝ) (p : Law (((B×A)⊕T)→β))
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (s : B→A) (i : ((B×A)⊕T)) : ℝ :=
  badIndexIndicator (J-entropy (map p (fun x=>x i)))
    (indexInformation p s i+indexCollision c s i) d e

omit [Nonempty A] in
lemma indexBad_own (J d e : ℝ) (p : Law (((B×A)⊕T)→β))
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (s : B→A) (b : B) (a i : A) :
    indexBad J d e p c (Function.update s b a) (Sum.inl (b,i))=
      indexBad J d e p c s (Sum.inl (b,i)) := by
  simp only [indexBad,indexInformation,indexCollision,Sum.elim_inl,
    blockInformation_own_independent,otherCollision_own]

omit [Nonempty A] in
lemma blockActive_sum (S : B→Finset A) (f : ((B×A)⊕T)→ℝ) :
    (∑ i∈blockActive S,f i)=(∑ b,∑ a∈S b,f (Sum.inl (b,a)))+∑ t,f (Sum.inr t) := by
  calc
    _ = ∑ i,if i∈blockActive S then f i else 0 := by
      simp only [Finset.sum_ite_mem,Finset.univ_inter]
    _ = _ := by
      rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
      simp only [mem_blockActive_left,mem_blockActive_right,ite_true,
        Finset.sum_ite_mem,Finset.univ_inter]

lemma mean_div {X : Type*} [Fintype X] (p : Law X) (f : X→ℝ) (d : ℝ) :
    mean p (fun x=>f x/d)=mean p f/d := by
  simp only [mean,mul_div_assoc,Finset.sum_div]

omit [Nonempty A] in
lemma indexInformation_sum (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (s : B→A) :
    (∑ i∈blockActive S,indexInformation p s i)=blockAllInformation p S s := by
  rw [blockActive_sum]
  rfl

omit [Nonempty A] in
lemma indexCollision_sum (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (S : B→Finset A) (s : B→A) :
    (∑ i∈blockActive S,indexCollision c s i)=allCollision c S s := by
  rw [blockActive_sum]
  rfl

omit [Nonempty A] in
lemma indexBad_sum (J d e : ℝ) (hd : 0<d) (he : 0<e)
    (p : Law (((B×A)⊕T)→β)) (hJ : ∀ i,entropy (map p (fun x=>x i))≤J)
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (hc : ∀ i j,0≤c i j)
    (S : B→Finset A) (s : B→A) :
    (∑ i∈blockActive S,indexBad J d e p c s i)≤
      blockAllDeficit J p S s/d+(blockAllInformation p S s+allCollision c S s)/e := by
  have hscore (i : ((B×A)⊕T)) : 0 ≤ indexInformation p s i+indexCollision c s i := by
    cases i with
    | inl z => exact add_nonneg (NNReal.coe_nonneg _) (Finset.sum_nonneg fun _ _=>hc _ _)
    | inr t => exact add_nonneg (NNReal.coe_nonneg _) (Finset.sum_nonneg fun _ _=>hc _ _)
  calc
    _ ≤ ∑ i∈blockActive S,((J-entropy (map p (fun x=>x i)))/d+
        (indexInformation p s i+indexCollision c s i)/e) :=
      Finset.sum_le_sum fun i _=>badIndexIndicator_le (sub_nonneg.mpr (hJ i)) (hscore i) hd he
    _ = _ := by
      rw [Finset.sum_add_distrib,←Finset.sum_div,←Finset.sum_div,Finset.sum_add_distrib,
        indexInformation_sum,indexCollision_sum]
      rfl

theorem selected_bad_fraction (J d e : ℝ)
    (p : Law (((B×A)⊕T)→β)) (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (S : B→Finset A) (r : ℕ) (hr : 0<r) (hS : ∀ b,r≤(S b).card) :
    r*mean (freshBlockLaw S) (fun s=>∑ b,indexBad J d e p c s (Sum.inl (b,s b)))≤
      mean (freshBlockLaw S) (fun s=>∑ i∈blockActive S,indexBad J d e p c s i) := by
  have hh:=fresh_selected_fraction S r hr hS
    (fun s b a=>indexBad J d e p c s (Sum.inl (b,a)))
    (fun _ _ _=>badIndexIndicator_nonneg _ _ _ _) (indexBad_own J d e p c)
  apply hh.trans
  apply mean_mono
  intro s
  rw [blockActive_sum]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>badIndexIndicator_nonneg _ _ _ _)

theorem fresh_bad_bound (J d e : ℝ) (hd : 0<d) (he : 0<e)
    (p : Law (((B×A)⊕T)→β)) (hJ : ∀ i,entropy (map p (fun x=>x i))≤J)
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (hc : ∀ i j,0≤c i j)
    (S : B→Finset A) (r : ℕ) (hr : 0<r) (hS : ∀ b,r≤(S b).card) :
    mean (freshBlockLaw S) (fun s=>∑ i∈blockActive S,indexBad J d e p c s i)≤
      mean (freshBlockLaw S) (blockAllDeficit J p S)/d+
      (mean (freshBlockLaw S) (blockAllInformation p S)+
        (∑ i∈blockActive S,∑ j∈blockActive S,c i j)/r)/e := by
  have hb:=mean_mono (freshBlockLaw S) (indexBad_sum J d e hd he p hJ c hc S)
  simp_rw [mean_add,mean_div] at hb
  apply hb.trans
  rw [mean_add]
  gcongr
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  apply (le_div_iff₀ hr').mpr
  simpa only [mul_comm] using fresh_all_collision_bound c hc S r hr hS

end SharpRamseyFive.FiniteEntropy

end

end OAI
