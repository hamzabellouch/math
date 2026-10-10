import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Marked

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

noncomputable def tv (p q : Ω → ℝ) : ℝ := (∑ s,|p s-q s|)/2

lemma tv_nonneg (p q : Ω → ℝ) : 0 ≤ tv p q := by
  unfold tv; positivity

lemma tv_symm (p q : Ω → ℝ) : tv p q=tv q p := by
  unfold tv
  simp_rw [abs_sub_comm]

lemma tv_triangle (p q r : Ω → ℝ) : tv p r ≤ tv p q+tv q r := by
  unfold tv
  rw [←add_div,←sum_add_distrib]
  exact div_le_div_of_nonneg_right (sum_le_sum (fun s _ => abs_sub_le _ _ _)) (by norm_num)

noncomputable def event (p : Ω → ℝ) (P : Ω → Prop) : ℝ := ∑ x,if P x then p x else 0

lemma event_nonneg (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (P : Ω → Prop) : 0 ≤ event p P := by
  unfold event; apply sum_nonneg; intro x _; split_ifs
  · exact hp x
  · exact le_rfl

theorem event_sub_le (p q : Ω → ℝ) (hs : ∑ x,p x=∑ x,q x) (P : Ω → Prop) :
    |event p P-event q P| ≤ tv p q := by
  let A : Finset Ω := univ.filter P
  have hz : ∑ x,(p x-q x)=0 := by rw [sum_sub_distrib,hs,sub_self]
  have he : event p P-event q P=∑ x ∈ A,(p x-q x) := by
    simp only [event,←sum_sub_distrib,A,sum_filter]
    apply sum_congr rfl
    intro x _
    split_ifs <;> simp
  have hc : ∑ x ∈ Aᶜ,(p x-q x)= -(∑ x ∈ A,(p x-q x)) := by
    have h := Finset.sum_add_sum_compl A (fun x => p x-q x)
    rw [hz] at h
    linarith
  have ha := abs_sum_le_sum_abs (fun x => p x-q x) A
  have hb := abs_sum_le_sum_abs (fun x => p x-q x) Aᶜ
  rw [hc,abs_neg] at hb
  have hab := Finset.sum_add_sum_compl A (fun x => |p x-q x|)
  rw [he]
  unfold tv
  linarith

noncomputable def bind (p : Ω → ℝ) (k : Ω → Ψ → ℝ) (y : Ψ) : ℝ := ∑ x,p x*k x y

omit [Fintype Ψ] in
lemma bind_nonneg (p : Ω → ℝ) (k : Ω → Ψ → ℝ)
    (hp : ∀ x,0 ≤ p x) (hk : ∀ x y,0 ≤ k x y) (y : Ψ) : 0 ≤ bind p k y :=
  sum_nonneg fun x _ => mul_nonneg (hp x) (hk x y)

lemma bind_sum (p : Ω → ℝ) (k : Ω → Ψ → ℝ) (hs : ∑ x,p x=1)
    (hk : ∀ x,∑ y,k x y=1) : ∑ y,bind p k y=1 := by
  unfold bind
  rw [sum_comm]
  simp_rw [←mul_sum,hk,mul_one]
  exact hs

lemma bind_contraction (p q : Ω → ℝ) (k : Ω → Ψ → ℝ)
    (hk : ∀ x y,0 ≤ k x y) (hs : ∀ x,∑ y,k x y=1) :
    tv (bind p k) (bind q k) ≤ tv p q := by
  unfold tv bind
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ = ∑ y,|∑ x,(p x-q x)*k x y| := by simp only [sub_mul,sum_sub_distrib]
    _ ≤ ∑ y,∑ x,|(p x-q x)*k x y| := sum_le_sum (fun y _ => abs_sum_le_sum_abs _ _)
    _ = _ := by
      rw [sum_comm]
      simp_rw [abs_mul,abs_of_nonneg (hk _ _),←mul_sum,hs,mul_one]

lemma bind_perturbation (p : Ω → ℝ) (k l : Ω → Ψ → ℝ)
    (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1) (ε : ℝ) (he : ∀ x,tv (k x) (l x) ≤ ε) :
    tv (bind p k) (bind p l) ≤ ε := by
  unfold tv bind
  have h : ∑ y,|∑ x,p x*k x y-∑ x,p x*l x y| ≤ 2*ε := by
    calc
      _ = ∑ y,|∑ x,p x*(k x y-l x y)| := by simp only [mul_sub,sum_sub_distrib]
      _ ≤ ∑ y,∑ x,|p x*(k x y-l x y)| := sum_le_sum (fun y _ => abs_sum_le_sum_abs _ _)
      _ = ∑ x,p x*(∑ y,|k x y-l x y|) := by
        rw [sum_comm]; simp_rw [abs_mul,abs_of_nonneg (hp _),←mul_sum]
      _ ≤ ∑ x,p x*(2*ε) := by
        apply sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (hp x)
        have hh := he x
        unfold tv at hh
        linarith
      _ = _ := by rw [←sum_mul,hs,one_mul]
  linarith

noncomputable def push (p : Ω → ℝ) (f : Ω → Ψ) (y : Ψ) : ℝ :=
  ∑ x,if f x=y then p x else 0

omit [Fintype Ψ] in
lemma push_nonneg (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (f : Ω → Ψ) (y : Ψ) :
    0 ≤ push p f y := by
  unfold push; apply sum_nonneg; intro x _; split_ifs
  · exact hp x
  · exact le_rfl

lemma push_sum (p : Ω → ℝ) (hs : ∑ x,p x=1) (f : Ω → Ψ) : ∑ y,push p f y=1 := by
  unfold push; rw [sum_comm]; simpa using hs

lemma push_contraction (p q : Ω → ℝ) (f : Ω → Ψ) : tv (push p f) (push q f) ≤ tv p q := by
  have he (r : Ω → ℝ) : push r f=bind r (fun x y => if f x=y then 1 else 0) := by
    funext y
    simp only [push,bind,mul_ite,mul_one,mul_zero]
  rw [he p,he q]
  exact
    bind_contraction p q (fun x y => if f x=y then 1 else 0)
      (fun x y => by split_ifs <;> norm_num) (fun x => by simp)

noncomputable def tensor (p : Ω → ℝ) (q : Ψ → ℝ) (x : Ω×Ψ) : ℝ := p x.1*q x.2

lemma tensor_tv (p q : Ω → ℝ) (r s : Ψ → ℝ)
    (hp : ∀ x,0 ≤ p x) (hps : ∑ x,p x=1) (hs : ∀ y,0 ≤ s y) (hss : ∑ y,s y=1) :
    tv (tensor p r) (tensor q s) ≤ tv p q+tv r s := by
  have hv (x : Ω) (y : Ψ) : |p x*r y-q x*s y| ≤ p x*|r y-s y|+|p x-q x| *s y := by
    have he : p x*r y-q x*s y=p x*(r y-s y)+(p x-q x)*s y := by ring
    rw [he]
    simpa only [abs_mul,abs_of_nonneg (hp x),abs_of_nonneg (hs y)] using abs_add_le (p x*(r y-s y)) ((p x-q x)*s y)
  unfold tv tensor
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ x,∑ y,(p x*|r y-s y|+|p x-q x| *s y) := sum_le_sum (fun x _ => sum_le_sum (fun y _ => hv x y))
    _ = _ := by simp_rw [sum_add_distrib,←mul_sum,hss,mul_one,←sum_mul,hps,one_mul]; ring

lemma tv_equiv (e : Ω ≃ Ψ) (p q : Ψ → ℝ) : tv (p ∘ e) (q ∘ e)=tv p q := by
  unfold tv
  rw [←e.sum_comp (fun y => |p y-q y|)]
  rfl

noncomputable def iid (p : Ω → ℝ) (n : ℕ) (x : Fin n → Ω) : ℝ := ∏ i,p (x i)

omit [Fintype Ω] in
lemma iid_nonneg (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (n : ℕ) (x : Fin n → Ω) : 0 ≤ iid p n x :=
  prod_nonneg fun _ _ => hp _

lemma iid_sum (p : Ω → ℝ) (hs : ∑ x,p x=1) (n : ℕ) : ∑ x,iid p n x=1 := by
  unfold iid
  rw [←Fintype.prod_sum]
  simp [hs]

theorem iid_tv (p q : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (hps : ∑ x,p x=1)
    (hq : ∀ x,0 ≤ q x) (hqs : ∑ x,q x=1) (n : ℕ) :
    tv (iid p n) (iid q n) ≤ n*tv p q := by
  induction n with
  | zero => simp [tv,iid]
  | succ n ih =>
    let e : (Ω×(Fin n → Ω)) ≃ (Fin (n+1) → Ω) := Fin.consEquiv (fun _ : Fin (n+1) => Ω)
    have hpE : iid p (n+1) ∘ e=tensor p (iid p n) := by
      funext x
      simp [iid,tensor,e,Fin.prod_univ_succ]
    have hqE : iid q (n+1) ∘ e=tensor q (iid q n) := by
      funext x
      simp [iid,tensor,e,Fin.prod_univ_succ]
    rw [←tv_equiv e,hpE,hqE]
    have ht := tensor_tv p q (iid p n) (iid q n) hp hps (iid_nonneg q hq n) (iid_sum q hqs n)
    push_cast
    nlinarith

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def product (p : I → Ω → ℝ) (x : I → Ω) : ℝ := ∏ i,p i (x i)

lemma product_marginal (p : I → Ω → ℝ) (hs : ∀ i,∑ a,p i a=1) (j : I) :
    push (product p) (fun x => x j)=p j := by
  classical
  funext y
  let q : I → Ω → ℝ := fun i a => if i=j then (if a=y then p i a else 0) else p i a
  have he (x : I → Ω) : (if x j=y then product p x else 0)=∏ i,q i (x i) := by
    by_cases h : x j=y
    · simp only [ite_eq_left h,product]
      apply prod_congr rfl
      intro i _
      by_cases hi : i=j
      · subst i; simp [q,h]
      · simp [q,hi]
    · simp only [ite_eq_right h]
      symm
      apply prod_eq_zero (mem_univ j)
      simp [q,h]
  have hq (i : I) : ∑ a,q i a=if i=j then p j y else 1 := by
    by_cases h : i=j
    · subst i; simp [q]
    · simp [q,h,hs i]
  unfold push
  simp_rw [he]
  rw [←Fintype.prod_sum]
  simp_rw [hq]
  simp

end Product


variable {B : Ω → Type*} [∀ a,Fintype (B a)]

noncomputable def sigmaLift (p : Ω → ℝ) (k : ∀ a,B a → ℝ) (s : Sigma B) : ℝ :=
  p s.1*k s.1 s.2

omit [Fintype Ω] [∀ a,Fintype (B a)] in
lemma sigmaLift_nonneg (p : Ω → ℝ) (k : ∀ a,B a → ℝ)
    (hp : ∀ a,0 ≤ p a) (hk : ∀ a b,0 ≤ k a b) (s : Sigma B) : 0 ≤ sigmaLift p k s :=
  mul_nonneg (hp _) (hk _ _)

lemma sigmaLift_sum (p : Ω → ℝ) (k : ∀ a,B a → ℝ)
    (hs : ∑ a,p a=1) (hk : ∀ a,∑ b,k a b=1) : ∑ s,sigmaLift p k s=1 := by
  simp only [sigmaLift,Fintype.sum_sigma,←mul_sum,hk,mul_one,hs]

lemma sigmaLift_tv (p q : Ω → ℝ) (k : ∀ a,B a → ℝ)
    (hk : ∀ a b,0 ≤ k a b) (hs : ∀ a,∑ b,k a b=1) :
    tv (sigmaLift p k) (sigmaLift q k)=tv p q := by
  simp only [tv,sigmaLift,Fintype.sum_sigma,←sub_mul,abs_mul,abs_of_nonneg (hk _ _),←mul_sum,hs,mul_one]


end MatchingFPRAS.Variation

namespace MatchingFPRAS.Transport

def tierBound (N D K : ℕ) : ℕ := N^2*(Nat.clog 2 D+2*K+2)

lemma base_block (N : ℕ) (hN : 0<N) : 2 ≤ (1+((N:ℝ)^2)⁻¹)^(N^2) := by
  have hp : (0:ℝ)<N := by exact_mod_cast hN
  have ha : -(2:ℝ)≤((N:ℝ)^2)⁻¹ := by
    have : (0:ℝ)≤((N:ℝ)^2)⁻¹ := by positivity
    linarith
  have h := one_add_mul_le_pow (a:=((N:ℝ)^2)⁻¹) ha (N^2)
  norm_cast at h
  have he : (N^2:ℝ)*((N:ℝ)^2)⁻¹=1 := mul_inv_cancel₀ (by positivity)
  norm_num only [Nat.cast_pow, he] at h
  linarith

lemma tierBound_reaches (N D K : ℕ) (hN : 0<N) :
    max (D:ℝ) (3*4^K) ≤ (1+((N:ℝ)^2)⁻¹)^(tierBound N D K) := by
  have hb := base_block N hN
  have hp : 0≤(1+((N:ℝ)^2)⁻¹)^(N^2) := by positivity
  have hD : (D:ℝ) ≤ 2^(Nat.clog 2 D) := by exact_mod_cast Nat.le_pow_clog (by decide : 1<2) D
  have hk : (3:ℝ)*4^K ≤ 2^(2*K+2) := by
    rw [pow_add,pow_mul]
    norm_num
    nlinarith [pow_pos (by norm_num : (0:ℝ)<4) K]
  have eD : Nat.clog 2 D ≤ Nat.clog 2 D+2*K+2 := by omega
  have eK : 2*K+2 ≤ Nat.clog 2 D+2*K+2 := by omega
  calc
    max (D:ℝ) (3*4^K) ≤ 2^(Nat.clog 2 D+2*K+2) := max_le
      (hD.trans (pow_le_pow_right₀ (by norm_num) eD))
      (hk.trans (pow_le_pow_right₀ (by norm_num) eK))
    _ ≤ _ := by
      unfold tierBound
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) hb _

noncomputable def ladderTier (N D K : ℕ) (hN : 0<N) : ℕ :=
  Nat.find (⟨tierBound N D K,tierBound_reaches N D K hN⟩ :
    ∃ t : ℕ,max (D:ℝ) (3*4^K) ≤ (1+((N:ℝ)^2)⁻¹)^t)

lemma ladderTier_spec (N D K : ℕ) (hN : 0<N) :
    max (D:ℝ) (3*4^K) ≤ (1+((N:ℝ)^2)⁻¹)^(ladderTier N D K hN) := by
  exact Nat.find_spec (p:=fun t : ℕ => max (D:ℝ) (3*4^K) ≤ (1+((N:ℝ)^2)⁻¹)^t)
    ⟨tierBound N D K,tierBound_reaches N D K hN⟩

lemma ladderTier_le (N D K : ℕ) (hN : 0<N) : ladderTier N D K hN ≤ tierBound N D K :=
  Nat.find_min' _ (tierBound_reaches N D K hN)

lemma ladderTier_min (N D K : ℕ) (hN : 0<N) {t : ℕ} (ht : t<ladderTier N D K hN) :
    (1+((N:ℝ)^2)⁻¹)^t < max (D:ℝ) (3*4^K) := lt_of_not_ge (Nat.find_min _ ht)

lemma topClamp_eq (N D K : ℕ) (hN : 0<N) (hD : 0<D) (w : ℝ)
    (hw : (D:ℝ)⁻¹ ≤ w ∧ w ≤ 3*4^K) :
    tierClamp (1+((N:ℝ)^2)⁻¹) (ladderTier N D K hN) w=w := by
  have ht := ladderTier_spec N D K hN
  have hlo : ((1+((N:ℝ)^2)⁻¹)^(ladderTier N D K hN))⁻¹ ≤ w :=
    (inv_anti₀ (by exact_mod_cast hD) ((le_max_left _ _).trans ht)).trans hw.1
  have hhi : w ≤ (1+((N:ℝ)^2)⁻¹)^(ladderTier N D K hN) := hw.2.trans ((le_max_right _ _).trans ht)
  simp only [tierClamp,min_eq_right hhi,max_eq_right hlo]

end MatchingFPRAS.Transport

namespace MatchingFPRAS.FiniteChain

open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma walk_nonneg (π : Ω → ℝ) (hp : ∀ a,0<π a) (C : Ω → Ω → ℝ)
    (hC : ∀ a b,0≤C a b) (z a : Ω) (n : ℕ) : 0 ≤ walk π C z n a := by
  induction n generalizing a with
  | zero => simp only [walk]; split_ifs <;> norm_num
  | succ n ih => exact sum_nonneg fun b _ => mul_nonneg (ih b) (div_nonneg (hC b a) (hp b).le)

lemma walk_sum (π : Ω → ℝ) (hp : ∀ a,0<π a) (C : Ω → Ω → ℝ)
    (hC : ∀ a,∑ b,C a b=π a) (z : Ω) (n : ℕ) : ∑ a,walk π C z n a=1 := by
  induction n with
  | zero => simp [walk]
  | succ n ih =>
    simp only [walk,kernel]
    rw [sum_comm]
    simp_rw [←mul_sum,←sum_div,hC,div_self (hp _).ne',mul_one]
    exact ih

end MatchingFPRAS.FiniteChain

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

def topSlot (T q : ℕ) (hq : 0<q) : Slot T q := toLex (0,⟨0,hq⟩)

lemma topSlot_tier (T q : ℕ) (hq : 0<q) : tier (topSlot T q hq)=T := by simp [tier,rank,topSlot]

omit [DecidableEq V] [DecidableEq J] in
lemma ladder_top_marginal (w : BagEdge bags → ℝ) (T q : ℕ) (hq : 0<q)
    (M : PM (BagEdge.Incident (bags := bags))) :
    Variation.push (ladderLaw w T q) (fun x => x (topSlot T q hq))=slotLaw w (topSlot T q hq) := by
  exact Variation.product_marginal (slotLaw w) (fun i => slotLaw_sum w i M) _

omit [DecidableEq V] [Fintype J] [DecidableEq J] in
lemma slotWeight_top (w : BagEdge bags → ℝ) (D K T q : ℕ) (hD : 0<D) (hq : 0<q)
    (hw : ∀ e,(D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K)
    (hT : max (D:ℝ) (3*4^K) ≤ (tierBase V)^T) :
    slotWeight w (topSlot T q hq)=w := by
  funext e
  have hlo : ((tierBase V)^T)⁻¹ ≤ w e :=
    (inv_anti₀ (by exact_mod_cast hD) ((le_max_left _ _).trans hT)).trans (hw e).1
  have hhi : w e ≤ (tierBase V)^T := (hw e).2.trans ((le_max_right _ _).trans hT)
  simp only [slotWeight,topSlot_tier,tierClamp,min_eq_right hhi,max_eq_right hlo]

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourcePM w K) := Classical.decEq _

noncomputable def revealLaw (w : V → V → ℝ) (K D : ℕ) (p : SourcePM w K → ℝ) : SourceMarked w K → ℝ :=
  Variation.sigmaLift p (Marking.conditional BagEdge.Incident (sourcePortions w K D))

lemma sourceBagWeight_pos (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (e : BagEdge (sourceBags w K)) : 0<sourceBagWeight w K D e := by
  unfold sourceBagWeight
  exact add_pos_of_nonneg_of_pos (sourceRealPortion_nonneg w hw K e) (div_pos (bagHeight_pos w K _) (by exact_mod_cast hD))

lemma revealLaw_ideal (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D) :
    revealLaw w K D (gibbs (sourceBagWeight w K D))=sourceLaw w K D := by
  funext a
  have hc (e : BagEdge (sourceBags w K)) : Marking.collapse (sourcePortions w K D) e≠0 := by
    rw [sourcePortions_collapse]
    exact (sourceBagWeight_pos w hw K D hD e).ne'
  have h := Marking.law_from_reveal BagEdge.Incident (sourcePortions w K D) hc a
  have he : Marking.collapse (sourcePortions w K D)=sourceBagWeight w K D :=
    sourcePortions_collapse w K D
  rw [he] at h
  have hz : Transport.partition (inc:=BagEdge.Incident) (sourceBagWeight w K D)=
      partitionWeight BagEdge.Incident (sourceBagWeight w K D) univ := by
    unfold Transport.partition partitionWeight matchingWeight
    congr 1
    ext M
    simp
  exact (show revealLaw w K D (gibbs (sourceBagWeight w K D)) a=
    sourceLaw w K D a from by
      unfold revealLaw Variation.sigmaLift gibbs matchingWeight
      rw [hz]
      exact h)

lemma revealLaw_tv (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (p q : SourcePM w K → ℝ) :
    Variation.tv (revealLaw w K D p) (revealLaw w K D q)=Variation.tv p q := by
  apply Variation.sigmaLift_tv
  · intro M a
    unfold Marking.conditional
    apply prod_nonneg
    intro e _
    apply div_nonneg (sourcePortions_nonneg w hw K D _ _)
    rw [sourcePortions_collapse]
    exact (sourceBagWeight_pos w hw K D hD e).le
  · intro M
    apply Marking.conditional_sum
    intro e
    rw [sourcePortions_collapse]
    exact (sourceBagWeight_pos w hw K D hD e).ne'

theorem source_marked_sampling (hn : 2 ≤ Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K : ℕ)
    (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K)
    (M₀ : SourcePM w K) (T : ℕ)
    (hT : max (sourceD (V:=V) K:ℝ) (3*4^K) ≤ (tierBase (SourceVertex V K))^T)
    (z : Slot T (ladderQ (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K)) → SourcePM w K)
    (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) :
    let D := sourceD (V:=V) K
    let N := Fintype.card (SourceVertex V K)
    let q := ladderQ N D
    ∃ hq : 0<q,
      let wt := sourceBagWeight w K D
      let ν := ladderLaw wt T q
      let C := ladderFlow (fun x a ha b hb => sourceBag_tree_adjacent w K hK x a b ha hb) (sourceTree_isTree w K).2 wt T q
      let p := Variation.push (MatchingFPRAS.FiniteChain.walk ν C z (ladderSteps N D K T ξ))
        (fun a => a (topSlot T q hq))
      Variation.tv (revealLaw w K D p) (sourceLaw w K D) ≤ ξ := by
  dsimp only
  let D := sourceD (V:=V) K
  let N := Fintype.card (SourceVertex V K)
  have hd : 0<D := lt_of_lt_of_le (by decide) (sourceD_one K)
  have hn' : 0<N := lt_of_lt_of_le (by decide : 0<2) (hn.trans (sourceVertex_card_ge K))
  have hq : 0<ladderQ N D := by unfold ladderQ ladderL; positivity
  refine ⟨hq,?_⟩
  rw [←revealLaw_ideal w hw K D hd,revealLaw_tv w hw K D hd]
  have hm := ladder_top_marginal (sourceBagWeight w K D) T (ladderQ N D) hq M₀
  have he := slotWeight_top (sourceBagWeight w K D) D K T (ladderQ N D) hd hq
    (sourceBagWeight_global w K D (sourceD_one K) hw hK) hT
  unfold slotLaw at hm
  rw [he] at hm
  change Variation.push (ladderLaw (sourceBagWeight w K D) T (ladderQ N D))
    (fun a => a (topSlot T (ladderQ N D) hq))=gibbs (sourceBagWeight w K D) at hm
  rw [←hm]
  apply (Variation.push_contraction _ _ _).trans
  exact source_ladder_sampling hn w hw K hK M₀ T z ξ hξ hξ1

end MatchingFPRAS.Enlargement

end OAI
