import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.Tv
import OAI.Combinatorics.MatchingCount.Sampling.Component

namespace OAI

namespace MatchingFPRAS.WeightedOptions

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def metropolisChoice (c : WeightedOptions Ω) (w : Ω → ℚ) (hw : ∀ a, 0 < w a) (a : Ω) :
    WeightedOptions Ω := c.accept a (fun b => min 1 (w b / w a))
      (fun b => le_min zero_le_one (div_nonneg (hw b).le (hw a).le))
      (fun _ => min_le_left _ _)

lemma real_law_sum (c : WeightedOptions Ω) : ∑ b, (c.law b : ℝ)=1 := by
  exact_mod_cast c.law_sum

lemma row_eq_of_off (f g : Ω → ℝ) (hf : ∑ x, f x=1) (hg : ∑ x, g x=1)
    (a : Ω) (h : ∀ b, a≠b → f b=g b) : f=g := by
  funext b
  by_cases hab : a=b
  · subst b
    have he : ∑ b ∈ univ.erase a, f b = ∑ b ∈ univ.erase a, g b := by
      apply sum_congr rfl
      intro b hb
      exact h b (ne_of_mem_erase hb).symm
    rw [←sum_erase_add _ _ (mem_univ a)] at hf hg
    linarith
  · exact h b hab

lemma min_ratio (x y : ℝ) (hx : 0 < x) : min (1:ℝ) (y/x) = min x y / x := by
  by_cases h : x≤y
  · rw [min_eq_left ((le_div_iff₀ hx).mpr (by simpa using h)),min_eq_left h,div_self hx.ne']
  · rw [min_eq_right ((div_le_one hx).mpr (le_of_not_ge h)),min_eq_right (le_of_not_ge h)]

theorem metropolisChoice_law (P : Replica.SymmetricProposal Ω) (c : Ω → WeightedOptions Ω)
    (hc : ∀ a b, ((c a).law b : ℝ)=P.q a b)
    (w : Ω → ℚ) (hw : ∀ a, 0 < w a) (a b : Ω) :
    (((c a).metropolisChoice w hw a).law b : ℝ) =
      Replica.metropolis P (fun x => (w x:ℝ)) a b := by
  have hpos : ∀ x, (0:ℝ)<w x := fun x => by exact_mod_cast hw x
  have hsum := real_law_sum ((c a).metropolisChoice w hw a)
  have he := row_eq_of_off _ _ hsum (Replica.metropolis_row P _ hpos a) a (fun b hab => ?_)
  · exact congrFun he b
  rw [metropolisChoice,accept_law,ite_eq_right hab,add_zero]
  push_cast
  rw [hc,min_ratio _ _ (hpos a)]
  simp only [Replica.metropolis,Replica.metropolisCapacity,ite_eq_right hab,Replica.offCapacity]
  ring

omit [Fintype Ω] [DecidableEq Ω] in
lemma metropolisChoice_size (c : WeightedOptions Ω) (w : Ω → ℚ) (hw : ∀ a, 0 < w a) (a : Ω) :
    (c.metropolisChoice w hw a).size = 2*c.size := by
  simp only [metropolisChoice,accept]
  omega

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

noncomputable def uniform (A : Type*) [Fintype A] (_ : A) : ℝ := 1/Fintype.card A

lemma uniform_nonneg (a : A) : 0≤uniform A a := by unfold uniform; positivity

lemma uniform_sum [Nonempty A] : ∑ a : A,uniform A a=1 := by
  simp only [uniform,sum_const,nsmul_eq_mul]
  exact mul_one_div_cancel (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card A:ℝ)≠0)

noncomputable def imageLaw (f : A → B) : B → ℝ := push (uniform A) f

omit [Fintype B] in
lemma imageLaw_nonneg (f : A → B) (b : B) : 0 ≤ imageLaw f b := push_nonneg _ uniform_nonneg _ _

lemma imageLaw_sum [Nonempty A] (f : A → B) : ∑ b,imageLaw f b=1 := push_sum _ uniform_sum _

omit [Fintype B] in
lemma imageLaw_eq_count (f : A → B) (b : B) :
    imageLaw f b=((univ.filter (fun a=>f a=b)).card:ℝ)/Fintype.card A := by
  simp only [imageLaw,push,uniform]
  rw [show (∑ x,if f x=b then (1:ℝ)/Fintype.card A else 0)=
    (∑ x,if f x=b then (1:ℝ) else 0)/Fintype.card A by
      simp only [sum_div,ite_div,zero_div]]
  simp

lemma imageLaw_equiv (e : A ≃ B) : imageLaw e=uniform B := by
  funext b
  unfold imageLaw push uniform
  rw [e.sum_comp (fun x=>if x=b then (1:ℝ)/Fintype.card A else 0)]
  simp [Fintype.card_congr e]

omit [Fintype C] in
lemma imageLaw_comp_equiv (e : A ≃ B) (f : B → C) : imageLaw (f ∘ e)=imageLaw f := by
  funext c
  unfold imageLaw push uniform
  rw [Fintype.card_congr e,←e.sum_comp (fun b=>if f b=c then (1:ℝ)/Fintype.card B else 0)]
  rfl

omit [Fintype C] in
lemma push_comp (p : A → ℝ) (f : A → B) (g : B → C) :
    push (push p f) g=push p (g ∘ f) := by
  funext c
  unfold push
  have h (b : B) : (if g b=c then ∑ a,if f a=b then p a else 0 else 0)=
      ∑ a,if g b=c then (if f a=b then p a else 0) else 0 := by
    by_cases hh : g b=c <;> simp [hh]
  simp_rw [h]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [←ite_and]
  rw [show (fun b=>if g b=c ∧ f a=b then p a else 0)=
    (fun b=>if f a=b then (if g b=c then p a else 0) else 0) by
      funext b; split_ifs <;> simp_all]
  simp

omit [Fintype C] in
lemma imageLaw_comp (f : A → B) (g : B → C) : imageLaw (g ∘ f)=push (imageLaw f) g :=
  (push_comp _ _ _).symm

lemma uniform_prod (a : A×B) : uniform (A×B) a=uniform A a.1*uniform B a.2 := by
  simp [uniform,Fintype.card_prod,Nat.cast_mul,mul_comm]

variable {D : Type*} [Fintype D]

omit [Fintype C] in
lemma imageLaw_pair (f : A → B → C) :
    imageLaw (fun x : A×B=>f x.1 x.2)=bind (uniform A) (fun a=>imageLaw (f a)) := by
  funext c
  simp only [imageLaw,push,bind,Fintype.sum_prod_type,uniform_prod,mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  split_ifs <;> simp

omit [Fintype C] in
lemma bind_push (p : A → ℝ) (f : A → B) (k : B → C → ℝ) :
    bind (push p f) k=bind p (fun a=>k (f a)) := by
  funext c
  simp only [bind,push,sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp

omit [Fintype C] in
lemma imageLaw_adaptive_pair (d : A → D) (f : D → B → C) :
    imageLaw (fun x : A×B=>f (d x.1) x.2)=bind (imageLaw d) (fun a=>imageLaw (f a)) := by
  rw [imageLaw_pair (fun a b=>f (d a) b), imageLaw,bind_push]

theorem uniform_sigma [Nonempty A] {E : B → Type*} [∀ b,Fintype (E b)]
    (e : (Σ b,E b) ≃ A) (z : A) :
    push (sigmaLift (fun b=>(Fintype.card (E b):ℝ)/Fintype.card A)
      (fun b=>uniform (E b))) e z=uniform A z := by
  have h (s : Sigma E) : sigmaLift (fun b=>(Fintype.card (E b):ℝ)/Fintype.card A)
      (fun b=>uniform (E b)) s=uniform (Sigma E) s := by
    have hn : (Fintype.card (E s.1):ℝ)≠0 := by
      let : Nonempty (E s.1) := ⟨s.2⟩
      exact_mod_cast Fintype.card_ne_zero
    simp only [sigmaLift,uniform,Fintype.card_congr e]
    field_simp
  have hh := congrArg (fun p=>push p e z) (funext h)
  rw [hh]
  exact congrFun (imageLaw_equiv e) z

open Finset
open scoped Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype C] in
lemma imageLaw_ignore [Nonempty A] (f : B → C) :
    imageLaw (fun x : A×B=>f x.2)=imageLaw f := by
  rw [imageLaw_pair (fun _ b=>f b)]
  funext c
  simp only [bind,←sum_mul,uniform_sum,one_mul]

omit [Fintype B] in
lemma push_sigmaLift {E : A → Type*} [∀ a,Fintype (E a)]
    (p : A → ℝ) (k : ∀ a,E a → ℝ) (f : (Σ a,E a) → B) :
    push (sigmaLift p k) f=bind p (fun a=>push (k a) (fun e=>f ⟨a,e⟩)) := by
  funext b
  simp only [push,sigmaLift,bind,Fintype.sum_sigma,mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro e _
  split_ifs <;> simp

lemma imageLaw_subsingleton [Nonempty A] [Subsingleton B] (f : A → B) :
    imageLaw f=uniform B := by
  let : Nonempty B := ⟨f (Classical.choice (inferInstance : Nonempty A))⟩
  funext b
  simp only [imageLaw,push,Subsingleton.elim (f _) b,ite_true,uniform_sum]
  let : Unique B := ⟨⟨b⟩,fun x=>Subsingleton.elim x b⟩
  simp [uniform]

lemma tv_self (p : A → ℝ) : tv p p=0 := by simp [tv]

open scoped Classical

lemma imageLaw_fin_skip {B C D : Type*} [Fintype B] [Nonempty B] [Fintype C] [Fintype D]
    (n : ℕ) (g : (Fin (n+2) → B) → C) (d : B → D) (f : D → (Fin n → B) → C)
    (hg : ∀ bits,g bits=f (d (bits (Fin.last (n+1)))) (fun i=>bits i.castSucc.castSucc)) :
    imageLaw g=bind (imageLaw d) (fun c=>imageLaw (f c)) := by
  let e : (B×(B×(Fin n → B))) ≃ (Fin (n+2) → B) :=
    (Equiv.prodCongr (Equiv.refl B) (Fin.snocEquiv (fun _ : Fin (n+1)=>B))).trans
      (Fin.snocEquiv (fun _ : Fin (n+2)=>B))
  have hE : g ∘ e=(fun x : B×(B×(Fin n→B))=>f (d x.1) x.2.2) := by
    funext x
    rw [Function.comp_apply,hg]
    simp [e,Fin.snocEquiv]

  rw [←imageLaw_comp_equiv e,hE,imageLaw_adaptive_pair d (fun c (u : B×(Fin n→B))=>f c u.2)]
  simp_rw [imageLaw_ignore]

end MatchingFPRAS.Variation

namespace MatchingFPRAS.WeightedOptions

open Finset Variation FiniteChoice

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def draw (c : WeightedOptions Ω) (k : ℕ) (bits : Fin k → Bool) : Ω :=
  c.out (chooseBits c.mass c.total k bits)

omit [Fintype Ω] [DecidableEq Ω] in
lemma chooseBits_imageLaw (c : WeightedOptions Ω) (k : ℕ) :
    imageLaw (chooseBits c.mass c.total k) = fun i => (tapeLaw c.mass c.total k i:ℝ) := by
  funext i
  rw [imageLaw_eq_count]
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,
    Nat.cast_ofNat,tapeLaw,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]
  congr 2
  congr 1
  ext bits
  simp only [mem_filter,mem_univ,true_and]

omit [Fintype Ω] in
lemma realLaw_push (c : WeightedOptions Ω) :
    (fun b => (c.law b:ℝ))=push (fun i=>(c.mass i:ℝ)) c.out := by
  funext b
  unfold law push
  simp only [Rat.cast_sum,apply_ite,Rat.cast_zero]

theorem draw_tv (c : WeightedOptions Ω) (k : ℕ) :
    tv (imageLaw (c.draw k)) (fun b=>(c.law b:ℝ)) ≤ 2*c.size/(2:ℝ)^k := by
  have h := fixed_bit_choice c.mass c.nonneg c.total k
  rw [←tapeLaw_eq] at h
  have hr : tv (fun i=>(tapeLaw c.mass c.total k i:ℝ)) (fun i=>(c.mass i:ℝ))
      ≤ 2*c.size/(2:ℝ)^k := by
    change (∑ i : Fin c.size, |(tapeLaw c.mass c.total k i:ℝ)-(c.mass i:ℝ)|)/2 ≤ _
    have hh := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_mul,
      Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow] using hh
  have hd : c.draw k = c.out ∘ chooseBits c.mass c.total k := rfl
  rw [hd,imageLaw_comp,realLaw_push,chooseBits_imageLaw]
  exact (push_contraction _ _ _).trans hr

def runDraw (c : ℕ → Ω → WeightedOptions Ω) (z : Ω) (k : ℕ) :
    (n : ℕ) → (Fin n → Fin k → Bool) → Ω
  | 0, _ => z
  | n+1, bits => (c n (runDraw c z k n (Fin.init bits))).draw k (bits (Fin.last n))

noncomputable def exactRun (c : ℕ → Ω → WeightedOptions Ω) (z : Ω) : ℕ → Ω → ℝ
  | 0 => fun b => if z=b then 1 else 0
  | n+1 => bind (exactRun c z n) (fun s b => ((c n s).law b:ℝ))

lemma exactRun_nonneg (c : ℕ → Ω → WeightedOptions Ω) (z : Ω) (n : ℕ) (b : Ω) :
    0≤exactRun c z n b := by
  induction n generalizing b with
  | zero => simp only [exactRun]; split_ifs <;> norm_num
  | succ n ih => exact bind_nonneg _ _ ih (fun s b => by exact_mod_cast (c n s).law_nonneg b) b

lemma exactRun_sum (c : ℕ → Ω → WeightedOptions Ω) (z : Ω) (n : ℕ) :
    ∑ b,exactRun c z n b=1 := by
  induction n with
  | zero => simp [exactRun]
  | succ n ih => exact bind_sum _ _ ih (fun s => real_law_sum (c n s))

omit [DecidableEq Ω] in
lemma runDraw_law (c : ℕ → Ω → WeightedOptions Ω) (z : Ω) (k n : ℕ) :
    imageLaw (runDraw c z k (n+1)) = bind (imageLaw (runDraw c z k n))
      (fun s => imageLaw ((c n s).draw k)) := by
  let e : ((Fin n → Fin k → Bool) × (Fin k → Bool)) ≃ (Fin (n+1) → Fin k → Bool) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Fin k → Bool))
  have h : runDraw c z k (n+1) ∘ e =
      (fun u => (c n (runDraw c z k n u.1)).draw k u.2) := by
    funext u
    change (c n (runDraw c z k n (Fin.init (Fin.snoc (α := fun _ : Fin (n+1) => Fin k → Bool) u.1 u.2)))).draw k
      (Fin.snoc (α := fun _ : Fin (n+1) => Fin k → Bool) u.1 u.2 (Fin.last n)) = _
    simp only [Fin.init_snoc,Fin.snoc_last]
  rw [←imageLaw_comp_equiv e,h]
  exact imageLaw_adaptive_pair (runDraw c z k n) (fun s bits => (c n s).draw k bits)

theorem runDraw_tv (c : ℕ → Ω → WeightedOptions Ω) (z : Ω) (k R n : ℕ)
    (hR : ∀ j s, (c j s).size ≤ R) :
    tv (imageLaw (runDraw c z k n)) (exactRun c z n) ≤ 2*n*R/(2:ℝ)^k := by
  induction n with
  | zero =>
    have h : imageLaw (runDraw c z k 0)=exactRun c z 0 := by
      funext b
      simp [imageLaw,push,Variation.uniform,runDraw,exactRun]
    rw [h,tv_self]
    norm_num
  | succ n ih =>
    rw [runDraw_law]
    change tv (bind _ _) (bind _ _)≤_
    let p := imageLaw (runDraw c z k n)
    let q := exactRun c z n
    let u := fun s => imageLaw ((c n s).draw k)
    let v := fun s b => ((c n s).law b:ℝ)
    have hu : ∀ s, tv (u s) (v s) ≤ 2*R/(2:ℝ)^k := by
      intro s
      exact ((c n s).draw_tv k).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hR n s) (by norm_num)) (by positivity))
    have h1 := bind_perturbation p u v (imageLaw_nonneg _) (imageLaw_sum _) _ hu
    have h2 := bind_contraction p q v
      (fun s b => by dsimp [v]; exact_mod_cast (c n s).law_nonneg b) (fun s => real_law_sum (c n s))
    calc
      _ ≤ tv (bind p u) (bind p v)+tv (bind p v) (bind q v) := tv_triangle _ _ _
      _ ≤ 2*R/(2:ℝ)^k+2*n*R/(2:ℝ)^k := add_le_add h1 (h2.trans ih)
      _ = _ := by push_cast; ring

end MatchingFPRAS.WeightedOptions

end OAI
