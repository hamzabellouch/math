import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Density

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

variable (p : I → Ω → ℝ)

noncomputable def mean (f : (I → Ω) → ℝ) : ℝ := ∑ s, density p s*f s

noncomputable def variance (f : (I → Ω) → ℝ) : ℝ :=
  dot p (f-(fun _ => mean p f)) (f-(fun _ => mean p f))

lemma mean_dot (f : (I → Ω) → ℝ) : mean p f = dot p (fun _ => 1) f := by simp [mean,dot]

lemma density_sum (hs : ∀ i, ∑ a, p i a = 1) : ∑ s, density p s = 1 := by
  unfold density
  rw [← Fintype.prod_sum]
  simp_rw [hs]
  simp

lemma mean_average (hs : ∀ i, ∑ a, p i a = 1) (i : I) (f : (I → Ω) → ℝ) :
    mean p (average p i f) = mean p f := by
  rw [mean_dot, ← average_adjoint]
  have ho : average p i (fun _ => 1) = (fun _ => 1) := by
    funext s; simpa [average_apply] using hs i
  rw [ho, ← mean_dot]

lemma mean_avgList (hs : ∀ i, ∑ a, p i a = 1) (l : List I) (f : (I → Ω) → ℝ) :
    mean p (avgList p l f) = mean p f := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [avgList_cons,mean_average p hs,ih]

omit [Fintype I] in
lemma average_update (i : I) (a : Ω) (f : (I → Ω) → ℝ) (s : I → Ω) :
    average p i f (Function.update s i a) = average p i f s := by
  simp only [average_apply,Function.update_idem]

lemma invariant_constant (f : (I → Ω) → ℝ) (hf : ∀ i, average p i f = f)
    (s t : I → Ω) : f s = f t := by
  classical
  have hu (i : I) (a : Ω) (s : I → Ω) : f (Function.update s i a) = f s := by
    rw [← hf i]
    exact average_update p i a f s
  have hpatch (S : Finset I) : f (fun i => if i ∈ S then t i else s i) = f s := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      have he : (fun j => if j ∈ insert i S then t j else s j) =
          Function.update (fun j => if j ∈ S then t j else s j) i (t i) := by
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [hji]
      rw [he,hu,ih]
  simpa using (hpatch Finset.univ).symm

lemma average_all (hs : ∀ i, ∑ a, p i a = 1) (l : List I) (hl : ∀ i, i ∈ l)
    (f : (I → Ω) → ℝ) : avgList p l f = (fun _ => mean p f) := by
  funext s
  have hc : ∀ t, avgList p l f t = avgList p l f s := fun t =>
    invariant_constant p (avgList p l f) (fun i => average_list_mem p hs l i (hl i) f) t s
  have hm := mean_avgList p hs l f
  unfold mean at hm
  simp_rw [hc] at hm
  rw [← Finset.sum_mul,density_sum p hs,one_mul] at hm
  exact hm

omit [Fintype I] in
lemma avgList_fixed (l : List I) (f : (I → Ω) → ℝ)
    (hf : ∀ i ∈ l, average p i f = f) : avgList p l f = f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [avgList_cons,ih (fun j hj => hf j (List.mem_cons_of_mem i hj)),hf i (List.mem_cons_self)]

omit [Fintype I] in
lemma avgList_comm_list (l k : List I) (f : (I → Ω) → ℝ) :
    avgList p l (avgList p k f) = avgList p k (avgList p l f) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [avgList_cons,ih,average_comm_list,avgList_cons]

omit [Fintype I] in
lemma avgList_congr (hs : ∀ i, ∑ a, p i a = 1) (l k : List I)
    (hmem : ∀ i, i ∈ l ↔ i ∈ k) (f : (I → Ω) → ℝ) : avgList p l f = avgList p k f := by
  have h₁ : avgList p l (avgList p k f) = avgList p k f :=
    avgList_fixed p l _ (fun i hi => average_list_mem p hs k i ((hmem i).mp hi) f)
  have h₂ : avgList p k (avgList p l f) = avgList p l f :=
    avgList_fixed p k _ (fun i hi => average_list_mem p hs l i ((hmem i).mpr hi) f)
  rw [avgList_comm_list,h₂] at h₁
  exact h₁

lemma projection_pythagoras (P : Projection p) (f : (I → Ω) → ℝ) :
    dot p (f-P.op f) (f-P.op f) = dot p f f-dot p (P.op f) (P.op f) := by
  rw [dot_sub_left p f (P.op f) (f-P.op f),dot_sub_right p f f (P.op f),
    dot_sub_right p (P.op f) f (P.op f),dot_comm p (P.op f) f,P.dot_image]
  ring

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω]

variable (p : I → Ω → ℝ)

noncomputable def future (S : Finset I) (x : I) := avgList p ((S.filter (x < ·)).toList)

noncomputable def increment (S : Finset I) (x : I) (f : (I → Ω) → ℝ) : (I → Ω) → ℝ :=
  future p S x f-average p x (future p S x f)

lemma martingale_partial (hs : ∀ i, ∑ a, p i a = 1) (S : Finset I) (f : (I → Ω) → ℝ) :
    (∑ x ∈ S, dot p (increment p S x f) (increment p S x f)) =
      dot p f f-dot p (avgList p S.toList f) (avgList p S.toList f) := by
  classical
  induction S using Finset.induction_on_min with
  | empty => simp [future,increment,avgList]
  | insert a S hmin ih =>
    have ha : a ∉ S := fun h => (lt_irrefl a) (hmin a h)
    have hfilter : (insert a S).filter (a < ·) = S := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hai⟩; rcases hi with rfl | hi
        · exact (lt_irrefl _ hai).elim
        · exact hi
      · intro hi; exact ⟨Or.inr hi,hmin i hi⟩
    have hother (x) (hx : x ∈ S) : (insert a S).filter (x < ·) = S.filter (x < ·) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hxi⟩; rcases hi with rfl | hi
        · exact (not_lt_of_gt (hmin x hx) hxi).elim
        · exact ⟨hi,hxi⟩
      · rintro ⟨hi,hxi⟩; exact ⟨Or.inr hi,hxi⟩
    have hc : avgList p (insert a S).toList f = average p a (avgList p S.toList f) := by
      change avgList p (insert a S).toList f = avgList p (a::S.toList) f
      apply avgList_congr p hs
      intro i; simp
    rw [Finset.sum_insert ha,hc]
    have hsum : (∑ x ∈ S, dot p (increment p (insert a S) x f)
        (increment p (insert a S) x f)) = ∑ x ∈ S, dot p (increment p S x f) (increment p S x f) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [increment,future,hother x hx]
    rw [hsum,ih]
    have hp := projection_pythagoras p (avgProjection p hs a) (avgList p S.toList f)
    change dot p (increment p (insert a S) a f) (increment p (insert a S) a f) + _ = _
    unfold increment future
    rw [hfilter]
    change dot p (avgList p S.toList f-average p a (avgList p S.toList f))
      (avgList p S.toList f-average p a (avgList p S.toList f)) =
      dot p (avgList p S.toList f) (avgList p S.toList f)-
        dot p (average p a (avgList p S.toList f)) (average p a (avgList p S.toList f)) at hp
    linarith

lemma martingale_variance (hs : ∀ i, ∑ a, p i a = 1) (f : (I → Ω) → ℝ) :
    variance p f = ∑ x, dot p (increment p Finset.univ x f) (increment p Finset.univ x f) := by
  rw [martingale_partial p hs]
  have hp := projection_pythagoras p (listProjection p hs Finset.univ.toList) f
  change dot p (f-avgList p Finset.univ.toList f) (f-avgList p Finset.univ.toList f) =
    dot p f f-dot p (avgList p Finset.univ.toList f) (avgList p Finset.univ.toList f) at hp
  rw [average_all p hs Finset.univ.toList (by simp)] at hp ⊢
  exact hp

omit [Fintype I] in
lemma increment_center (hs : ∀ i, ∑ a, p i a = 1) (S : Finset I) (x : I) (f : (I → Ω) → ℝ) :
    average p x (increment p S x f) = 0 := by
  simp [increment,map_sub,average_idem p hs]

lemma average_pair_future (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (hxy : x < y)
    (f : (I → Ω) → ℝ) : average p y (pairCondition p x y f) = future p Finset.univ x f := by
  change avgList p (y::outside x y) f = avgList p ((Finset.univ.filter (x < ·)).toList) f
  apply avgList_congr p hs
  intro i
  simp only [List.mem_cons,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,outside]
  constructor
  · rintro (rfl | ⟨hi,_⟩)
    · exact hxy
    · exact hi
  · intro hi
    by_cases hiy : i=y
    · exact Or.inl hiy
    · exact Or.inr ⟨hi,hiy⟩

lemma increment_pair_formula (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (hxy : x < y)
    (f : (I → Ω) → ℝ) : increment p Finset.univ x f =
      average p y (pairCondition p x y f)-average p x (average p y (pairCondition p x y f)) := by
  rw [average_pair_future p hs x y hxy]
  rfl

end

section

open Finset

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

noncomputable def localEnergy (q : Ω → Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  (∑ a, ∑ b, q a b * (f a-f b)^2)/2

lemma localEnergy_nonneg (q : Ω → Ω → ℝ) (hq : ∀ a b, 0 ≤ q a b) (f : Ω → ℝ) :
    0 ≤ localEnergy q f := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg
    (fun b _ => mul_nonneg (hq a b) (sq_nonneg _)))) (by norm_num)

lemma localEnergy_sub (q : Ω → Ω → ℝ) (hq : ∀ a b, 0 ≤ q a b) (f g : Ω → ℝ) :
    localEnergy q (f-g) ≤ 2*localEnergy q f+2*localEnergy q g := by
  unfold localEnergy
  have h : (∑ a, ∑ b, q a b*((f-g) a-(f-g) b)^2) ≤
      ∑ a, ∑ b, (2*(q a b*(f a-f b)^2)+2*(q a b*(g a-g b)^2)) := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    have hsq : ((f a-g a)-(f b-g b))^2 ≤ 2*(f a-f b)^2+2*(g a-g b)^2 := by
      nlinarith [sq_nonneg ((f a-f b)+(g a-g b))]
    change q a b*((f a-g a)-(f b-g b))^2 ≤ _
    calc
      _ ≤ q a b*(2*(f a-f b)^2+2*(g a-g b)^2) := mul_le_mul_of_nonneg_left hsq (hq a b)
      _ = _ := by ring
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
  linarith

lemma localEnergy_shift (q : Ω → Ω → ℝ) (f : Ω → ℝ) (c : ℝ) :
    localEnergy q (fun a => f a-c) = localEnergy q f := by
  unfold localEnergy
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  congr 2; ring

lemma square_average (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (f : A → ℝ) :
    (∑ a, w a*f a)^2 ≤ ∑ a, w a*(f a)^2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun a => w a*f a) (f := w) (g := fun a => w a*(f a)^2)
    (fun a _ => hw a) (fun a _ => mul_nonneg (hw a) (sq_nonneg _))
    (fun a _ => by nlinarith [sq_nonneg (w a*f a)])
  simpa only [hs,one_mul] using h

lemma localEnergy_average (q : Ω → Ω → ℝ) (hq : ∀ a b, 0 ≤ q a b)
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (f : A → Ω → ℝ) :
    localEnergy q (fun a => ∑ i, w i*f i a) ≤ ∑ i, w i*localEnergy q (f i) := by
  have h : (∑ a, ∑ b, q a b*((∑ i, w i*f i a)-(∑ i, w i*f i b))^2) ≤
      ∑ a, ∑ b, q a b*(∑ i, w i*(f i a-f i b)^2) := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    apply mul_le_mul_of_nonneg_left _ (hq a b)
    simpa only [mul_sub,Finset.sum_sub_distrib] using square_average w hw hs (fun i => f i a-f i b)
  have he : (∑ a, ∑ b, q a b*(∑ i, w i*(f i a-f i b)^2)) =
      ∑ i, w i*(∑ a, ∑ b, q a b*(f i a-f i b)^2) := by
    simp only [Finset.mul_sum]
    have hin (a : Ω) : (∑ b, ∑ i, q a b*(w i*(f i a-f i b)^2)) =
        ∑ i, ∑ b, q a b*(w i*(f i a-f i b)^2) := Finset.sum_comm
    simp_rw [hin]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  unfold localEnergy
  rw [he] at h
  have := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 2)
  simpa only [Finset.sum_div,mul_div_assoc] using this

lemma localEnergy_bound (π : Ω → ℝ) (q : Ω → Ω → ℝ) (hq : ∀ a b, 0 ≤ q a b)
    (hr : ∀ a, ∑ b, q a b = π a) (hc : ∀ b, ∑ a, q a b = π b) (f : Ω → ℝ) :
    localEnergy q f ≤ 2*∑ a, π a*(f a)^2 := by
  have hh : (∑ a, ∑ b, q a b*(f a-f b)^2) ≤
      ∑ a, ∑ b, (2*(q a b*(f a)^2)+2*(q a b*(f b)^2)) := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    have hs : (f a-f b)^2 ≤ 2*(f a)^2+2*(f b)^2 := by nlinarith [sq_nonneg (f a+f b)]
    calc
      _ ≤ q a b * (2 * (f a)^2 + 2 * (f b)^2) :=
        mul_le_mul_of_nonneg_left hs (hq a b)
      _ = _ := by ring
  have hleft : (∑ a, ∑ b, q a b*(f a)^2) = ∑ a, π a*(f a)^2 := by
    simp only [← Finset.sum_mul,hr]
  have hright : (∑ a, ∑ b, q a b*(f b)^2) = ∑ b, π b*(f b)^2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,hc]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,hleft,hright] at hh
  unfold localEnergy; linarith

end

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

variable (p : I → Ω → ℝ)

omit [DecidableEq I] [Fintype Ω] in
lemma density_nonneg (hp : ∀ i a, 0 ≤ p i a) (s : I → Ω) : 0 ≤ density p s :=
  Finset.prod_nonneg (fun i _ => hp i (s i))

lemma mean_mono (hp : ∀ i a, 0 ≤ p i a) {f g : (I → Ω) → ℝ}
    (h : ∀ s, f s ≤ g s) : mean p f ≤ mean p g :=
  Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h s) (density_nonneg p hp s))

lemma mean_nonneg (hp : ∀ i a, 0 ≤ p i a) {f : (I → Ω) → ℝ} (h : ∀ s, 0 ≤ f s) :
    0 ≤ mean p f := Finset.sum_nonneg (fun s _ => mul_nonneg (density_nonneg p hp s) (h s))

lemma mean_add (f g : (I → Ω) → ℝ) : mean p (f+g) = mean p f+mean p g := by
  simp [mean,mul_add,Finset.sum_add_distrib]

lemma mean_mul (c : ℝ) (f : (I → Ω) → ℝ) : mean p (fun s => c*f s) = c*mean p f := by
  simp only [mean,Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring

lemma mean_square (f : (I → Ω) → ℝ) : mean p (fun s => (f s)^2) = dot p f f := by
  simp only [mean,dot]; apply Finset.sum_congr rfl; intro s _; ring

structure PairCapacity (x y : I) where
  q : (Ω × Ω) → (Ω × Ω) → ℝ
  nonneg : ∀ a b, 0 ≤ q a b
  row : ∀ a, ∑ b, q a b = p x a.1*p y a.2
  col : ∀ b, ∑ a, q a b = p x b.1*p y b.2

def replacePair (x y : I) (s : I → Ω) (a : Ω × Ω) : I → Ω :=
  Function.update (Function.update s x a.1) y a.2

def slice (x y : I) (f : (I → Ω) → ℝ) (s : I → Ω) (a : Ω × Ω) : ℝ :=
  f (replacePair x y s a)

noncomputable def pairEnergy (x y : I) (Q : PairCapacity p x y) (f : (I → Ω) → ℝ) : ℝ :=
  mean p (fun s => localEnergy Q.q (slice x y f s))

omit [Fintype I] [Fintype Ω] in
lemma slice_sub (x y : I) (f g : (I → Ω) → ℝ) (s : I → Ω) :
    slice x y (f-g) s = slice x y f s-slice x y g s := rfl

lemma pairEnergy_nonneg (hp : ∀ i a, 0 ≤ p i a) (x y : I) (Q : PairCapacity p x y)
    (f : (I → Ω) → ℝ) : 0 ≤ pairEnergy p x y Q f :=
  mean_nonneg p hp (fun _ => localEnergy_nonneg Q.q Q.nonneg _)

lemma pairEnergy_sub (hp : ∀ i a, 0 ≤ p i a) (x y : I) (Q : PairCapacity p x y)
    (f g : (I → Ω) → ℝ) : pairEnergy p x y Q (f-g) ≤
      2*pairEnergy p x y Q f+2*pairEnergy p x y Q g := by
  have hh := mean_mono p hp (fun s => localEnergy_sub Q.q Q.nonneg (slice x y f s) (slice x y g s))
  change mean p (fun s => localEnergy Q.q (slice x y (f-g) s)) ≤
    mean p ((fun s => 2*localEnergy Q.q (slice x y f s))+(fun s => 2*localEnergy Q.q (slice x y g s))) at hh
  rw [mean_add,mean_mul,mean_mul] at hh
  exact hh

lemma slice_square_mean (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    mean p (fun s => ∑ a : Ω × Ω, (p x a.1*p y a.2)*(slice x y f s a)^2) = dot p f f := by
  have he (s : I → Ω) : (∑ a : Ω × Ω, (p x a.1*p y a.2)*(slice x y f s a)^2) =
      average p x (average p y (fun s => (f s)^2)) s := by
    rw [Fintype.sum_prod_type]
    simp only [average_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    unfold slice replacePair; ring
  simp_rw [he]
  rw [mean_average p hs,mean_average p hs,mean_square]

lemma pairEnergy_bound (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (x y : I) (Q : PairCapacity p x y) (f : (I → Ω) → ℝ) :
    pairEnergy p x y Q f ≤ 2*dot p f f := by
  have hh := mean_mono p hp (fun s => localEnergy_bound (fun a => p x a.1*p y a.2)
    Q.q Q.nonneg Q.row Q.col (slice x y f s))
  rw [mean_mul,slice_square_mean p hs] at hh
  exact hh

omit [Fintype I] [Fintype Ω] in
lemma replacePair_update (i x y : I) (hix : i ≠ x) (hiy : i ≠ y)
    (s : I → Ω) (a : Ω × Ω) (b : Ω) :
    replacePair x y (Function.update s i b) a = Function.update (replacePair x y s a) i b := by
  unfold replacePair
  rw [Function.update_comm hix,Function.update_comm hiy]

omit [Fintype I] in
lemma slice_average (i x y : I) (hix : i ≠ x) (hiy : i ≠ y)
    (f : (I → Ω) → ℝ) (s : I → Ω) :
    slice x y (average p i f) s = (fun a => ∑ b, p i b*slice x y f (Function.update s i b) a) := by
  funext a
  simp only [slice,average_apply,replacePair_update i x y hix hiy]

lemma pairEnergy_average (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (i x y : I) (hix : i ≠ x) (hiy : i ≠ y) (Q : PairCapacity p x y) (f : (I → Ω) → ℝ) :
    pairEnergy p x y Q (average p i f) ≤ pairEnergy p x y Q f := by
  have hh (s : I → Ω) : localEnergy Q.q (slice x y (average p i f) s) ≤
      average p i (fun s => localEnergy Q.q (slice x y f s)) s := by
    rw [slice_average p i x y hix hiy]
    exact localEnergy_average Q.q Q.nonneg (p i) (hp i) (hs i) (fun b => slice x y f (Function.update s i b))
  have hh := mean_mono p hp hh
  rw [mean_average p hs] at hh
  exact hh

lemma pairEnergy_avgList (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (l : List I) (x y : I) (hl : ∀ i ∈ l, i ≠ x ∧ i ≠ y) (Q : PairCapacity p x y)
    (f : (I → Ω) → ℝ) : pairEnergy p x y Q (avgList p l f) ≤ pairEnergy p x y Q f := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih =>
    rw [avgList_cons]
    exact (pairEnergy_average p hp hs i x y (hl i (by simp)).1 (hl i (by simp)).2 Q _).trans
      (ih (fun j hj => hl j (List.mem_cons_of_mem i hj)))

end MatchingFPRAS.Replica

end OAI
