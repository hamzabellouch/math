import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.MetropolisChoice

namespace OAI

namespace MatchingFPRAS.Replica

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

omit [Fintype I] [Fintype Ω] [DecidableEq Ω] in
lemma replacePair_at (x y : I) (hxy : x≠y) (s : I → Ω) (a : Ω×Ω) :
    ((replacePair x y s a) x,(replacePair x y s a) y)=a := by
  simp [replacePair,hxy]

omit [Fintype I] [Fintype Ω] [DecidableEq Ω] in
lemma replacePair_idem (x y : I) (s : I → Ω) (a b : Ω×Ω) :
    replacePair x y (replacePair x y s a) b = replacePair x y s b := by
  funext i
  by_cases hy : i=y
  · subst i; simp [replacePair]
  · by_cases hx : i=x
    · subst i; simp [replacePair,hy]
    · simp [replacePair,hx,hy]

noncomputable def pairStep (x y : I) (Q : PairCapacity p x y) (s t : I → Ω) : ℝ :=
  ∑ b : Ω×Ω, if replacePair x y s b=t then Q.q (s x,s y) b/(p x (s x)*p y (s y)) else 0

noncomputable def baseStep (i : I) (s t : I → Ω) : ℝ :=
  ∑ a : Ω, if Function.update s i a=t then p i a else 0

lemma local_pairFlow (hp : ∀ i a, 0<p i a) (hs : ∀ i,∑ a,p i a=1)
    (x y : I) (hxy : x≠y) (Q : PairCapacity p x y) (s t : I → Ω) :
    pairFlow p x y Q s t = density p s*pairStep p x y Q s t := by
  let f : (I → Ω) → ℝ := fun r => if r=s then pairStep p x y Q r t else 0
  have hf := slice_mean p hs x y f
  have hmean : mean p f=density p s*pairStep p x y Q s t := by
    simp only [mean,f,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true]
  rw [hmean] at hf
  rw [←hf]
  unfold pairFlow pushedFlow mean
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  rw [Fintype.sum_prod_type,mul_sum]
  apply sum_congr rfl
  intro a _
  have hpa : ((replacePair x y r a) x,(replacePair x y r a) y)=a := replacePair_at x y hxy r a
  rcases a with ⟨ax,ay⟩
  have hx : (replacePair x y r (ax,ay)) x=ax := congrArg Prod.fst hpa
  have hy : (replacePair x y r (ax,ay)) y=ay := congrArg Prod.snd hpa
  by_cases ha : replacePair x y r (ax,ay)=s
  · simp only [f,ha,ite_true]
    rw [←ha]
    simp only [pairStep,hx,hy,replacePair_idem,mul_sum]
    apply sum_congr rfl
    intro b _
    by_cases hb : replacePair x y r b=t
    · simp only [ha,hb,ite_true]
      field_simp [ne_of_gt (hp x ax),ne_of_gt (hp y ay)]
    · simp only [Prod.mk.injEq,ha,hb,true_and,ite_false,mul_zero]
  · simp only [f,ite_eq_right ha,mul_zero]
    apply sum_eq_zero
    intro b _
    simp only [Prod.mk.injEq,ha,false_and,ite_false]

lemma local_baseFlow (_hp : ∀ i a,0<p i a) (hs : ∀ i,∑ a,p i a=1)
    (i : I) (s t : I → Ω) : baseFlow p i s t=density p s*baseStep p i s t := by
  let f : (I → Ω) → ℝ := fun r => if r=s then baseStep p i r t else 0
  have hf := mean_average p hs i f
  have hmean : mean p f=density p s*baseStep p i s t := by
    simp only [mean,f,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true]
  rw [hmean] at hf
  rw [←hf]
  unfold baseFlow pushedFlow mean
  rw [Fintype.sum_prod_type]
  simp only [average_apply]
  apply sum_congr rfl
  intro r _
  rw [Fintype.sum_prod_type,mul_sum]
  apply sum_congr rfl
  intro a _
  by_cases ha : Function.update r i a=s
  · simp only [f,ite_eq_left ha]
    rw [←ha]
    simp only [baseStep,Function.update_idem,mul_sum]
    apply sum_congr rfl
    intro b _
    by_cases hb : Function.update r i b=t
    · simp only [ha,hb,ite_true]
    · simp only [Prod.mk.injEq,ha,hb,true_and,ite_false,mul_zero]
  · simp only [f,ite_eq_right ha,mul_zero]
    apply sum_eq_zero
    intro b _
    simp only [Prod.mk.injEq,ha,false_and,ite_false]

noncomputable def localScan (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y,PairCapacity p x y) (s t : I → Ω) : ℝ :=
  (if s=t then (1:ℝ) else 0)/2+
    ((∑ x,∑ y ∈ guides x,pairStep p x y (Q x y) s t)+∑ i ∈ base,baseStep p i s t)/
      (2*(updateCount guides base:ℝ))

theorem localScan_kernel (hp : ∀ i a,0<p i a) (hs : ∀ i,∑ a,p i a=1)
    (guides : I → Finset I) (hself : ∀ x y,y∈guides x → x≠y) (base : Finset I)
    (Q : ∀ x y,PairCapacity p x y) (s t : I → Ω) :
    localScan p guides base Q s t=FiniteChain.kernel (density p) (scanFlow p guides base Q) s t := by
  have hpos : 0<density p s := prod_pos fun i _=>hp i (s i)
  have hpair : (∑ x,∑ y ∈ guides x,pairFlow p x y (Q x y) s t)=
      density p s*(∑ x,∑ y ∈ guides x,pairStep p x y (Q x y) s t) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y hy
    exact local_pairFlow p hp hs x y (hself x y hy) (Q x y) s t
  have hbase : (∑ i ∈ base,baseFlow p i s t)=density p s*(∑ i ∈ base,baseStep p i s t) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro i hi
    exact local_baseFlow p hp hs i s t
  unfold FiniteChain.kernel scanFlow localScan
  rw [hpair,hbase]
  have hn := ne_of_gt hpos
  by_cases hst : s=t
  · subst t
    simp only [ite_true]
    field_simp [hn]
  · simp only [ite_eq_right hst,zero_div]
    field_simp [hn]
    ring

end MatchingFPRAS.Replica

namespace MatchingFPRAS.WeightedOptions

open Finset Variation

variable {J Ω B : Type*} [Fintype J] [DecidableEq J] [Fintype Ω] [DecidableEq Ω]

variable [Fintype B] [Nonempty B]

def drawThen (c : WeightedOptions J) (g : J → B → Ω) (k : ℕ)
    (bits : (Fin k → Bool) × B) : Ω := g (c.draw k bits.1) bits.2

omit [DecidableEq J] [Fintype Ω] [DecidableEq Ω] [Nonempty B] in
lemma drawThen_law [DecidableEq J] [Fintype Ω] [DecidableEq Ω] [Nonempty B]
    (c : WeightedOptions J) (g : J → B → Ω) (k : ℕ) :
    imageLaw (c.drawThen g k)=bind (imageLaw (c.draw k)) (fun j=>imageLaw (g j)) :=
  imageLaw_adaptive_pair (c.draw k) g

theorem drawThen_tv (c : WeightedOptions J) (g : J → B → Ω) (k : ℕ)
    (P : J → Ω → ℝ) (hn : ∀ j x,0≤P j x) (hs : ∀ j,∑ x,P j x=1)
    (e : ℝ) (he : ∀ j,tv (imageLaw (g j)) (P j)≤e) :
    tv (imageLaw (c.drawThen g k)) (bind (fun j=>(c.law j:ℝ)) P)≤
      2*c.size/(2:ℝ)^k+e := by
  rw [drawThen_law]
  calc
    _ ≤ tv (bind (imageLaw (c.draw k)) (fun j=>imageLaw (g j)))
        (bind (imageLaw (c.draw k)) P)+
        tv (bind (imageLaw (c.draw k)) P) (bind (fun j=>(c.law j:ℝ)) P) := tv_triangle _ _ _
    _ ≤ e+2*c.size/(2:ℝ)^k := add_le_add
      (bind_perturbation _ _ _ (imageLaw_nonneg _) (imageLaw_sum _) e he)
      ((bind_contraction _ _ P hn hs).trans (c.draw_tv k))
    _ = _ := add_comm _ _

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Replica

open Finset Variation

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

abbrev Update (I : Type*) := (I×I) ⊕ I

def updates (guides : I → Finset I) (base : Finset I) : Finset (Update I) :=
  ((univ : Finset (I×I)).filter (fun ij=>ij.2∈guides ij.1)).disjSum base

lemma updates_card (guides : I → Finset I) (base : Finset I) :
    (updates guides base).card=updateCount guides base := by
  simp only [updates,card_disjSum,updateCount]
  congr 1
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  simp

lemma updates_nonempty (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty) :
    (updates guides base).Nonempty := by
  obtain ⟨i,hi⟩:=hb
  exact ⟨Sum.inr i,by simp [updates,hi]⟩

variable (p : I → Ω → ℝ)

noncomputable def updateKernel (Q : ∀ x y,PairCapacity p x y) (s : I → Ω) :
    Option (Update I) → (I → Ω) → ℝ
  | none,t => if s=t then 1 else 0
  | some (.inl ij),t => pairStep p ij.1 ij.2 (Q ij.1 ij.2) s t
  | some (.inr i),t => baseStep p i s t

lemma pairStep_nonneg (hp : ∀ i a,0<p i a) (x y : I) (Q : PairCapacity p x y) (s t : I → Ω) :
    0≤pairStep p x y Q s t := by
  apply sum_nonneg
  intro b _
  split_ifs
  · exact div_nonneg (Q.nonneg _ _) (mul_nonneg (hp _ _).le (hp _ _).le)
  · exact le_rfl

lemma pairStep_sum (hp : ∀ i a,0<p i a) (x y : I) (Q : PairCapacity p x y) (s : I → Ω) :
    ∑ t,pairStep p x y Q s t=1 := by
  unfold pairStep
  rw [sum_comm]
  simp only [sum_ite_eq,mem_univ,ite_true]
  rw [←sum_div,Q.row]
  exact div_self (mul_pos (hp _ _) (hp _ _)).ne'

lemma baseStep_nonneg (hp : ∀ i a,0≤p i a) (i : I) (s t : I → Ω) : 0≤baseStep p i s t := by
  apply sum_nonneg
  intro a _
  split_ifs
  · exact hp _ _
  · exact le_rfl

lemma baseStep_sum (hs : ∀ i,∑ a,p i a=1) (i : I) (s : I → Ω) :
    ∑ t,baseStep p i s t=1 := by
  unfold baseStep
  rw [sum_comm]
  simpa using hs i

lemma updateKernel_nonneg (hp : ∀ i a,0<p i a) (Q : ∀ x y,PairCapacity p x y)
    (s : I → Ω) (u : Option (Update I)) (t : I → Ω) : 0≤updateKernel p Q s u t := by
  cases u with
  | none => dsimp [updateKernel]; split_ifs <;> norm_num
  | some u => cases u with
    | inl ij => exact pairStep_nonneg p hp _ _ _ _ _
    | inr i => exact baseStep_nonneg p (fun i a=>(hp i a).le) _ _ _

lemma updateKernel_sum (hp : ∀ i a,0<p i a) (hs : ∀ i,∑ a,p i a=1)
    (Q : ∀ x y,PairCapacity p x y) (s : I → Ω) (u : Option (Update I)) :
    ∑ t,updateKernel p Q s u t=1 := by
  cases u with
  | none => simp [updateKernel]
  | some u => cases u with
    | inl ij => exact pairStep_sum p hp _ _ _ _
    | inr i => exact baseStep_sum p hs _ _

variable [LinearOrder (Update I)]

def scanChoice (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty) :
    WeightedOptions (Option (Update I)) :=
  WeightedOptions.mix (1/2) (by norm_num) (by norm_num) (WeightedOptions.pure none)
    ((WeightedOptions.uniform (updates guides base) (updates_nonempty guides base hb)).map some)

lemma scanChoice_size (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty) :
    (scanChoice guides base hb).size=1+updateCount guides base := by
  simp only [scanChoice,WeightedOptions.mix,WeightedOptions.map,WeightedOptions.pure,
    WeightedOptions.uniform,updates_card]

lemma scanChoice_law (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty)
    (Q : ∀ x y,PairCapacity p x y) (s t : I → Ω) :
    bind (fun u=>((scanChoice guides base hb).law u:ℝ)) (updateKernel p Q s) t=
      localScan p guides base Q s t := by
  unfold Variation.bind
  rw [Fintype.sum_option]
  simp only [scanChoice,WeightedOptions.mix_law,WeightedOptions.pure_law,
    WeightedOptions.map_law]
  simp only [Option.some.injEq,reduceCtorEq,ite_false,sum_const_zero,mul_zero,zero_add]
  simp only [sum_ite_eq',mem_univ,ite_true,WeightedOptions.uniform_law]
  push_cast
  rw [updates_card]
  simp only [updateKernel,Fintype.sum_sum_type,Fintype.sum_prod_type,updates,
    inl_mem_disjSum,inr_mem_disjSum,
    mem_filter,mem_univ,true_and]
  unfold localScan
  simp only [apply_ite,Rat.cast_inv,Rat.cast_natCast,Rat.cast_zero,
    ite_mul,zero_mul,mul_zero,sum_ite_mem,univ_inter]
  simp only [←mul_sum]
  by_cases h : s=t <;> simp only [h,ite_true,ite_false] <;> ring



open Finset Variation

variable {I Ω B : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable [Fintype B] [Nonempty B]

def localSampler (pair : I → I → (Ω×Ω) → B → Ω×Ω) (refresh : I → B → Ω)
    (s : I → Ω) : Option (Update I) → B → (I → Ω)
  | none,_ => s
  | some (.inl ij),b => replacePair ij.1 ij.2 s (pair ij.1 ij.2 (s ij.1,s ij.2) b)
  | some (.inr i),b => Function.update s i (refresh i b)

lemma localSampler_tv (p : I → Ω → ℝ) (Q : ∀ x y,PairCapacity p x y)
    (pair : I → I → (Ω×Ω) → B → Ω×Ω) (refresh : I → B → Ω) (e : ℝ) (he : 0≤e)
    (hp : ∀ x y a,tv (imageLaw (pair x y a)) (fun b=>(Q x y).q a b/(p x a.1*p y a.2))≤e)
    (hr : ∀ i,tv (imageLaw (refresh i)) (p i)≤e) (s : I → Ω) (u : Option (Update I)) :
    tv (imageLaw (localSampler pair refresh s u)) (updateKernel p Q s u)≤e := by
  cases u with
  | none =>
    have h : imageLaw (localSampler pair refresh s none)=updateKernel p Q s none := by
      funext t
      simp only [imageLaw,push,localSampler,updateKernel]
      by_cases hst : s=t
      · subst t
        simpa using uniform_sum (A:=B)
      · simp [hst]
    rw [h,tv_self]
    exact he
  | some u => cases u with
    | inl ij =>
      have hk : updateKernel p Q s (some (.inl ij))=
          push (fun b=>(Q ij.1 ij.2).q (s ij.1,s ij.2) b/(p ij.1 (s ij.1)*p ij.2 (s ij.2)))
            (replacePair ij.1 ij.2 s) := by
        funext t
        simp only [updateKernel,pairStep,push]
      rw [hk]
      change tv (imageLaw ((replacePair ij.1 ij.2 s) ∘ pair ij.1 ij.2 (s ij.1,s ij.2)))
        (push (fun b=>(Q ij.1 ij.2).q (s ij.1,s ij.2) b/(p ij.1 (s ij.1)*p ij.2 (s ij.2)))
          (replacePair ij.1 ij.2 s))≤e
      rw [imageLaw_comp]
      exact (push_contraction _ _ _).trans (hp _ _ _)
    | inr i =>
      have hk : updateKernel p Q s (some (.inr i))=push (p i) (Function.update s i) := by
        funext t
        simp only [updateKernel,baseStep,push]
        apply sum_congr rfl
        intro a _
        congr 1
      rw [hk]
      change tv (imageLaw ((Function.update s i) ∘ refresh i)) (push (p i) (Function.update s i))≤e
      rw [imageLaw_comp]
      exact (push_contraction _ _ _).trans (hr i)

variable [LinearOrder (Update I)]

def sampleScan (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty)
    (pair : I → I → (Ω×Ω) → B → Ω×Ω) (refresh : I → B → Ω) (k : ℕ) (s : I → Ω) :
    ((Fin k → Bool) × B) → (I → Ω) :=
  (scanChoice guides base hb).drawThen (localSampler pair refresh s) k

theorem sampleScan_tv (p : I → Ω → ℝ) (hp : ∀ i a,0<p i a) (hs : ∀ i,∑ a,p i a=1)
    (guides : I → Finset I) (hself : ∀ x y,y∈guides x → x≠y)
    (base : Finset I) (hb : base.Nonempty) (Q : ∀ x y,PairCapacity p x y)
    (pair : I → I → (Ω×Ω) → B → Ω×Ω) (refresh : I → B → Ω) (e : ℝ) (he : 0≤e)
    (hpr : ∀ x y a,tv (imageLaw (pair x y a)) (fun b=>(Q x y).q a b/(p x a.1*p y a.2))≤e)
    (hr : ∀ i,tv (imageLaw (refresh i)) (p i)≤e) (k : ℕ) (s : I → Ω) :
    tv (imageLaw (sampleScan guides base hb pair refresh k s))
      (FiniteChain.kernel (density p) (scanFlow p guides base Q) s)≤
      2*(1+updateCount guides base)/(2:ℝ)^k+e := by
  have ht := WeightedOptions.drawThen_tv (scanChoice guides base hb) (localSampler pair refresh s)
    k (updateKernel p Q s) (updateKernel_nonneg p hp Q s) (updateKernel_sum p hp hs Q s)
    e (localSampler_tv p Q pair refresh e he hpr hr s)
  have hl : Variation.bind (fun u=>((scanChoice guides base hb).law u:ℝ)) (updateKernel p Q s)=
      FiniteChain.kernel (density p) (scanFlow p guides base Q) s := by
    funext t
    rw [scanChoice_law,localScan_kernel p hp hs guides hself base Q]
  rw [hl,scanChoice_size] at ht
  simpa only [Nat.cast_add,Nat.cast_one,sampleScan] using ht

end MatchingFPRAS.Replica

namespace MatchingFPRAS.Variation

open Finset

variable {Ω B : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype B] [Nonempty B]

def runSample (g : Ω → B → Ω) (z : Ω) : (n : ℕ) → (Fin n → B) → Ω
  | 0,_ => z
  | n+1,bits => g (runSample g z n (Fin.init bits)) (bits (Fin.last n))

omit [DecidableEq Ω] [Nonempty B] in
lemma runSample_law [DecidableEq Ω] [Nonempty B] (g : Ω → B → Ω) (z : Ω) (n : ℕ) :
    imageLaw (runSample g z (n+1))=bind (imageLaw (runSample g z n)) (fun s=>imageLaw (g s)) := by
  let e : ((Fin n → B) × B) ≃ (Fin (n+1) → B) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _=>B))
  have h : runSample g z (n+1) ∘ e=(fun u=>g (runSample g z n u.1) u.2) := by
    funext u
    change g (runSample g z n (Fin.init (Fin.snoc (α:=fun _ : Fin (n+1)=>B) u.1 u.2)))
      (Fin.snoc (α:=fun _ : Fin (n+1)=>B) u.1 u.2 (Fin.last n))=_
    simp only [Fin.init_snoc,Fin.snoc_last]
  rw [←imageLaw_comp_equiv e,h]
  exact imageLaw_adaptive_pair (runSample g z n) g

theorem runSample_walk_tv (π : Ω → ℝ) (C : Ω → Ω → ℝ)
    (hn : ∀ s t,0≤FiniteChain.kernel π C s t) (hs : ∀ s,∑ t,FiniteChain.kernel π C s t=1)
    (g : Ω → B → Ω) (d : ℝ)
    (hd : ∀ s,tv (imageLaw (g s)) (FiniteChain.kernel π C s)≤d) (z : Ω) (n : ℕ) :
    tv (imageLaw (runSample g z n)) (FiniteChain.walk π C z n)≤n*d := by
  induction n with
  | zero =>
    have h : imageLaw (runSample g z 0)=FiniteChain.walk π C z 0 := by
      funext b
      by_cases hb : b=z
      · subst b; simp [imageLaw,push,uniform,runSample,FiniteChain.walk]
      · simp [imageLaw,push,runSample,FiniteChain.walk,hb,Ne.symm hb]
    rw [h,tv_self]
    simp
  | succ n ih =>
    rw [runSample_law]
    change tv (bind _ _) (bind _ _)≤_
    calc
      _ ≤ tv (bind (imageLaw (runSample g z n)) (fun s=>imageLaw (g s)))
          (bind (imageLaw (runSample g z n)) (FiniteChain.kernel π C))+
          tv (bind (imageLaw (runSample g z n)) (FiniteChain.kernel π C))
            (bind (FiniteChain.walk π C z n) (FiniteChain.kernel π C)) := tv_triangle _ _ _
      _ ≤ d+n*d := add_le_add
        (bind_perturbation _ _ _ (imageLaw_nonneg _) (imageLaw_sum _) d hd)
        ((bind_contraction _ _ _ hn hs).trans ih)
      _ = _ := by push_cast; ring

end MatchingFPRAS.Variation

end OAI
