import OAI.Combinatorics.HadwigerCounterexample.QuadraticFourier

namespace OAI

/-! # Polynomial Zero Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {A I J : Type} [Fintype A] [DecidableEq A]

def poly1 (s : Finset A) (x : Vec A) := ∏ i∈s,x i

def Stocks (A : Type) (d : ℕ) : Space (Vec (Vec A)) :=
  open Classical in Submodule.span F {x | ∃ s : Finset A,s.card ≤ d ∧ x = poly1 s}

theorem stocks_rise (A : Type) [Fintype A] [DecidableEq A] {d j : ℕ} (h : d≤j) :
    Stocks A d≤ Stocks A j := span_mono (fun _ ⟨s,hx,h'⟩=> ⟨s,hx.trans h,h'⟩)
theorem stocks_one (A : Type) [Fintype A] [DecidableEq A] (d : ℕ) (b : F) :
    (fun _ : Vec A=>b)∈ Stocks A d := by
  have hh : poly1 (∅:Finset A)∈ Stocks A d := subset_span ⟨_,by simp,rfl⟩
  have he : b • poly1 (∅:Finset A)=(fun _ : Vec A=>b) := by ext; simp [poly1]
  rw [←he]; exact Submodule.smul_mem _ _ hh
omit [Fintype A] [DecidableEq A] in
theorem stock_var (i : A) : (fun x : Vec A => x i)∈Stocks A 1 :=
  subset_span ⟨{i},by simp,by funext; simp [poly1]⟩

omit [Fintype A] in
theorem poly1_union (x : Vec A) (s t : Finset A) :
    poly1 (s∪t) x=poly1 s x*poly1 t x := by
  have he (x : Vec A) (s : Finset A) (i : A) :
      poly1 (insert i s) x=x i*poly1 s x := by
    by_cases h : i∈s
    · rw [insert_eq_of_mem h]
      unfold poly1; rw [← Finset.mul_prod_erase _ _ h,←mul_assoc,bit_sq]
    simp [poly1,h]
  induction s using Finset.induction_on with
  | empty => simp [poly1]
  | insert i s hi ih => rw [insert_union,he,he,ih,mul_assoc]

omit [Fintype A] in
set_option maxHeartbeats 600000 in
theorem stock_prod {f g : Vec (Vec A)} {d j : ℕ} (hf : f∈ Stocks A d) (hg : g∈Stocks A j) :
    f*g∈Stocks A (d+j) := by
  classical
  unfold Stocks at hf
  induction hf using Submodule.span_induction with
  | zero => simp
  | add f j _ _ hf hj => rw [add_mul]; exact Submodule.add_mem _ hf hj
  | smul p j _ hj =>
    rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hj
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    unfold Stocks at hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t,ht,rfl⟩ := hx
      exact subset_span ⟨s∪t,(Finset.card_union_le ..).trans (add_le_add hs ht),
        funext fun x=>(poly1_union x s t).symm⟩
    | zero => simp
    | add f j _ _ hf hj => rw [mul_add]; exact Submodule.add_mem _ hf hj
    | smul p j _ hj => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hj

def spoil (p : Vec A) : Vec (Vec A) →ₗ[F] Vec (Vec A) where
  toFun f := fun i => f (i+p)-f i
  map_add' a b := funext fun i=>by simp only [Pi.add_apply]; ring
  map_smul' a b := funext fun i=>by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

set_option maxHeartbeats 600000 in
theorem stock_decay (p : Vec A) {d : ℕ} {f} (h : f∈ Stocks A (d+1)) :
    spoil p f ∈ Stocks A d := by
  classical
  unfold Stocks at h
  induction h using Submodule.span_induction with
  | zero => simp
  | add f j _ _ hf hj => rw [map_add]; exact Submodule.add_mem _ hf hj
  | smul p j _ hj => rw [map_smul]; exact Submodule.smul_mem _ _ hj
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    induction s using Finset.induction_on generalizing d with
    | empty =>
      have hi : spoil p (poly1 ∅)=0 := by funext; simp [spoil,poly1]
      rw [hi]; exact Submodule.zero_mem _
    | insert i s hi ih =>
      rw [card_insert_of_notMem hi] at hs
      have he : poly1 s∈ Stocks A d := subset_span ⟨_,by omega,rfl⟩
      let u := poly1 s
      let v := fun x : Vec A => x i+p i
      have hh :
          spoil p (poly1 (insert i s))=p i • u + v*spoil p u := by
        funext x; simp only [v,u,spoil,LinearMap.coe_mk,AddHom.coe_mk,
          poly1,Finset.prod_insert hi,Pi.smul_apply,Pi.add_apply,smul_eq_mul,Pi.mul_apply]; ring
      rw [hh]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ he) ?_
      cases d
      next =>
        obtain rfl : s=∅ := Finset.card_eq_zero.mp (by omega)
        have hi : spoil p u=0 := by funext; simp [spoil,u,poly1]
        rw [hi]; simp
      next d =>
        have hS : spoil p u∈ Stocks A d := ih (by omega)
        have hf : v∈ Stocks A 1 := Submodule.add_mem (Stocks A 1)
          (stock_var i) (stocks_one A 1 (p i))
        have hm := stock_prod hf hS
        rwa [Nat.add_comm 1] at hm

omit [Fintype A] [DecidableEq A] in
theorem stock_initial {f} (x y : Vec A) (h : f∈ Stocks A 0) : f x=f y := by
  unfold Stocks at h
  induction h using Submodule.span_induction with
  | zero => rfl
  | add f j _ _ hf hj => simp only [Pi.add_apply,hf,hj]
  | smul p j _ hj => simp only [Pi.smul_apply,hj]
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    obtain rfl : s=∅ := Finset.card_eq_zero.mp (by omega)
    simp [poly1]

theorem stocks_bound (A : Type) [Fintype A] [DecidableEq A] (d : ℕ) (f : Vec (Vec A))
    (h : f∈ Stocks A d) (he : ∃ x, f x≠0) :
    bp (-(d:ℝ))≤ pr unif (fun x => f x≠0) := by
  classical
  induction d generalizing f with
  | zero =>
    obtain ⟨x,hx⟩ := he
    have he (y:Vec A) : f y≠0 := (stock_initial y x h).trans_ne hx
    simp only [pr,ind_one (he _), Nat.cast_zero, neg_zero,bp_zero,unif_law.avg_const,le_refl]
  | succ d ih =>
    by_cases hh : ∃ y, f y=0
    · obtain ⟨x,hx⟩ := he; obtain ⟨y,hy⟩ := hh
      let p := x-y
      have hZ : bp (-(d:ℝ))≤ pr unif (fun x=>spoil p f x≠0) := ih _ (stock_decay p h)
        ⟨y,by change f (y+p)-f y≠0; unfold p; rw [add_sub_cancel,hy,sub_zero]; exact hx⟩
      let P x := f x≠0
      have hg :
          pr unif (fun x=>spoil p f x≠0)≤2*pr unif P := by
        have he x (h : spoil p f x≠0) :
            P (x+p)∨P x := by
          by_contra! hh; unfold spoil at h; apply h
          unfold P at hh; simp [not_ne_iff.mp hh.1,not_ne_iff.mp hh.2]
        apply ((pr_mono unif_law.nz he).trans (pr_or_le unif_law.nz)).trans_eq
        rw [show pr unif (fun x=>P (x+p))=pr unif P from phase_trans p (fun x=>ind (P x)),two_mul]
      have hx' := hZ.trans hg
      push_cast
      rw [neg_add,bp_add,bp_neg 1,bp_one]
      linarith only [hx']
    have hz (x:Vec A) : f x≠0 := fun he=>hh ⟨x,he⟩
    simp only [pr,ind_one (hz _),unif_law.avg_const]
    rw [←bp_zero]; exact bp_le (by apply neg_nonpos.mpr; positivity)
end HadwigerCounterexample

end

end OAI
