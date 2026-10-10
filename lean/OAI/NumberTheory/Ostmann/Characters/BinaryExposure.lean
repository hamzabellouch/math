import OAI.NumberTheory.Ostmann.Characters.BinaryHaar

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.BinaryExposure
attribute [local instance] Classical.propDecidable

def avg {α:Type*} [Fintype α] (f:α→ℝ) : ℝ := (Fintype.card α:ℝ)⁻¹*∑a,f a

theorem avg_nonneg {α:Type*} [Fintype α] (f:α→ℝ) (hf:∀a,0≤f a) : 0≤avg f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun a _=>hf a))

theorem avg_mono {α:Type*} [Fintype α] (f g:α→ℝ) (h:∀a,f a≤g a) : avg f≤avg g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _=>h a)) (by positivity)

theorem avg_const {α:Type*} [Fintype α] [Nonempty α] (c:ℝ) : avg (fun _:α=>c)=c := by
  have hn : (Fintype.card α:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [avg,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem avg_prod {α β:Type*} [Fintype α] [Fintype β] (f:α×β→ℝ) :
    avg f=avg (fun a:α=>avg (fun b:β=>f (a,b))) := by
  simp only [avg,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem avg_mul_const {α:Type*} [Fintype α] (f:α→ℝ) (c:ℝ) :
    avg (fun a=>f a*c)=avg f*c := by
  simp only [avg,← Finset.sum_mul,mul_assoc]

theorem avg_const_mul {α:Type*} [Fintype α] (f:α→ℝ) (c:ℝ) :
    avg (fun a=>c*f a)=c*avg f := by
  simp only [avg,← Finset.mul_sum]
  ring

theorem avg_indicator {α:Type*} [Fintype α] (P:α→Prop) :
    avg (fun a=>if P a then 1 else 0)=(Nat.card {a:α//P a}:ℝ)/Nat.card α := by
  simp [avg,Nat.card_eq_fintype_card,Fintype.card_subtype,div_eq_mul_inv,mul_comm]

variable {G H:Type*} [Group G] [Fintype G]

@[reducible] def admissible (c:ℕ→H→G→G→Prop) (left right:ℕ→H→G→G→H) :
    (k:ℕ)→H→G→BinaryHaar.Splits G k→Prop
  | 0,_,_,_ => True
  | k+1,h,t,z => c k h t z.1 ∧
      admissible c left right k (left k h t z.1) z.1 z.2.1 ∧
      admissible c left right k (right k h t z.1) (z.1⁻¹*t) z.2.2

def probability (c:ℕ→H→G→G→Prop) (left right:ℕ→H→G→G→H) :
    ℕ→H→G→ℝ
  | 0,_,_ => 1
  | k+1,h,t => avg (fun x:G=>(if c k h t x then 1 else 0)*
      probability c left right k (left k h t x) x *
      probability c left right k (right k h t x) (x⁻¹*t))

theorem probability_nonneg (c:ℕ→H→G→G→Prop) (left right:ℕ→H→G→G→H)
    (k:ℕ) (h:H) (t:G) : 0≤probability c left right k h t := by
  induction k generalizing h t with
  | zero => exact zero_le_one
  | succ k ih =>
    apply avg_nonneg
    intro x
    exact mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (ih _ _)) (ih _ _)

theorem probability_eq_count (c:ℕ→H→G→G→Prop) (left right:ℕ→H→G→G→H)
    (k:ℕ) (h:H) (t:G) :
    probability c left right k h t=
      (Nat.card {z:BinaryHaar.Splits G k//admissible c left right k h t z}:ℝ)/
        Nat.card (BinaryHaar.Splits G k) := by
  refine (show probability c left right k h t =
      avg (fun z : BinaryHaar.Splits G k =>
        if admissible c left right k h t z then 1 else 0) from ?_).trans
    (avg_indicator (fun z : BinaryHaar.Splits G k => admissible c left right k h t z))
  induction k generalizing h t with
  | zero =>
    let : Nonempty (BinaryHaar.Splits G 0) := ⟨PUnit.unit⟩
    have he := avg_const (α:=BinaryHaar.Splits G 0) (1:ℝ)
    simpa only [probability,admissible,ite_true] using he.symm
  | succ k ih =>
    simp only [probability,admissible]
    rw [avg_prod]
    apply congrArg avg
    funext x
    rw [avg_prod,ih,ih]
    symm
    calc
      _ = avg (fun z:BinaryHaar.Splits G k=>
          ((if c k h t x then 1 else 0)*
            (if admissible c left right k (left k h t x) x z then 1 else 0))*
          avg (fun z':BinaryHaar.Splits G k=>
            if admissible c left right k (right k h t x) (x⁻¹*t) z' then 1 else 0)) := by
        apply congrArg avg
        funext z
        rw [← avg_const_mul]
        apply congrArg avg
        funext z'
        split_ifs <;> simp_all
      _ = _ := by rw [avg_mul_const,avg_const_mul]

def bound (b:ℕ→ℝ) : ℕ→ℝ
  | 0 => 1
  | k+1 => b k*(bound b k)^2

theorem probability_le (c:ℕ→H→G→G→Prop) (left right:ℕ→H→G→G→H)
    (b:ℕ→ℝ) (hb:∀k,0≤b k)
    (hc:∀k h t,(Nat.card {x:G//c k h t x}:ℝ)/Nat.card G≤b k)
    (k:ℕ) (h:H) (t:G) : probability c left right k h t≤bound b k := by
  have hbound : ∀k,0≤bound b k := by
    intro k
    induction k with
    | zero => exact zero_le_one
    | succ k ih => exact mul_nonneg (hb k) (sq_nonneg _)
  induction k generalizing h t with
  | zero => exact le_rfl
  | succ k ih =>
    apply le_trans (avg_mono _
      (fun x:G=>(if c k h t x then 1 else 0)*(bound b k)^2) ?_)
    · rw [avg_mul_const,avg_indicator]
      exact mul_le_mul_of_nonneg_right (hc k h t) (sq_nonneg _)
    · intro x
      by_cases hx:c k h t x
      · simp only [hx,ite_true,one_mul,pow_two]
        exact mul_le_mul (ih _ _) (ih _ _)
          (probability_nonneg c left right k _ _) (hbound k)
      · simp only [hx,ite_false,zero_mul,le_refl]

theorem count_le (c:ℕ→H→G→G→Prop) (left right:ℕ→H→G→G→H)
    (b:ℕ→ℝ) (hb:∀k,0≤b k)
    (hc:∀k h t,(Nat.card {x:G//c k h t x}:ℝ)/Nat.card G≤b k)
    (k:ℕ) (h:H) (t:G) :
    (Nat.card {z:BinaryHaar.Splits G k//admissible c left right k h t z}:ℝ)/
      Nat.card (BinaryHaar.Splits G k)≤bound b k := by
  rw [← probability_eq_count]
  exact probability_le c left right b hb hc k h t

end Ostmann.Characters.BinaryExposure

end

end OAI
