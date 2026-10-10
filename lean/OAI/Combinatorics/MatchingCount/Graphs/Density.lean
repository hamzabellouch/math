import Mathlib

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

noncomputable def density (p : I → Ω → ℝ) (s : I → Ω) : ℝ := ∏ i, p i (s i)

noncomputable def dot (p : I → Ω → ℝ) (f g : (I → Ω) → ℝ) : ℝ :=
  ∑ s, density p s * f s * g s

noncomputable def average (p : I → Ω → ℝ) (i : I) :
    (((I → Ω) → ℝ) →ₗ[ℝ] ((I → Ω) → ℝ)) where
  toFun f s := ∑ a, p i a * f (Function.update s i a)
  map_add' f g := by funext s; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by funext s; simp [Finset.mul_sum,mul_left_comm]

omit [Fintype I] in
lemma average_apply (p : I → Ω → ℝ) (i : I) (f : (I → Ω) → ℝ) (s : I → Ω) :
    average p i f s = ∑ a, p i a * f (Function.update s i a) := rfl

omit [Fintype I] in
lemma average_idem (p : I → Ω → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (i : I)
    (f : (I → Ω) → ℝ) : average p i (average p i f) = average p i f := by
  funext s
  simp only [average_apply, Function.update_idem]
  rw [← Finset.sum_mul, hp i, one_mul]

omit [Fintype I] in
lemma average_comm (p : I → Ω → ℝ) (i j : I) (f : (I → Ω) → ℝ) :
    average p i (average p j f) = average p j (average p i f) := by
  classical
  by_cases h : i = j
  · subst j; rfl
  funext s
  simp only [average_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [Function.update_comm h]
  ring

noncomputable def swapDraw (i : I) : ((I → Ω) × Ω) ≃ ((I → Ω) × Ω) where
  toFun z := (Function.update z.1 i z.2, z.1 i)
  invFun z := (Function.update z.1 i z.2, z.1 i)
  left_inv z := by simp [Function.update_idem]
  right_inv z := by simp [Function.update_idem]

omit [Fintype Ω] in
lemma density_swap (p : I → Ω → ℝ) (i : I) (s : I → Ω) (a : Ω) :
    density p s * p i a = density p (Function.update s i a) * p i (s i) := by
  classical
  unfold density
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase i, p j (Function.update s i a j)) =
      ∏ j ∈ Finset.univ.erase i, p j (s j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  ring

lemma average_adjoint (p : I → Ω → ℝ) (i : I) (f g : (I → Ω) → ℝ) :
    dot p (average p i f) g = dot p f (average p i g) := by
  classical
  unfold dot
  simp only [average_apply, Finset.mul_sum, Finset.sum_mul]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  have h := Equiv.sum_comp (swapDraw (Ω := Ω) i)
    (fun z : (I → Ω) × Ω => density p z.1 * f z.1 * (p i z.2 * g (Function.update z.1 i z.2)))
  rw [← h]
  apply Finset.sum_congr rfl
  intro z _
  simp only [swapDraw, Equiv.coe_fn_mk, Function.update_idem,
    Function.update_eq_self]
  have hz := density_swap p i z.1 z.2
  nlinarith [congrArg (fun t : ℝ => t * f (Function.update z.1 i z.2) * g z.1) hz]

variable (p : I → Ω → ℝ)

lemma dot_comm (f g : (I → Ω) → ℝ) : dot p f g = dot p g f := by
  unfold dot; apply Finset.sum_congr rfl; intro s _; ring

lemma dot_zero_left (f : (I → Ω) → ℝ) : dot p 0 f = 0 := by simp [dot]

lemma dot_zero_right (f : (I → Ω) → ℝ) : dot p f 0 = 0 := by simp [dot]

lemma dot_add_left (f g h : (I → Ω) → ℝ) :
    dot p (f+g) h = dot p f h + dot p g h := by
  simp [dot, mul_add, add_mul, Finset.sum_add_distrib]

lemma dot_add_right (f g h : (I → Ω) → ℝ) :
    dot p f (g+h) = dot p f g + dot p f h := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_sub_left (f g h : (I → Ω) → ℝ) :
    dot p (f-g) h = dot p f h - dot p g h := by
  simp [dot, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma dot_sub_right (f g h : (I → Ω) → ℝ) :
    dot p f (g-h) = dot p f g - dot p f h := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

lemma dot_const_left (c : ℝ) (g : (I → Ω) → ℝ) :
    dot p (fun _ => c) g = c * dot p (fun _ => 1) g := by
  simp only [dot, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _; ring

lemma dot_nonneg (hp : ∀ i a, 0 ≤ p i a) (f : (I → Ω) → ℝ) : 0 ≤ dot p f f := by
  apply Finset.sum_nonneg
  intro s _
  have hh : 0 ≤ density p s := Finset.prod_nonneg (fun i _ => hp i (s i))
  nlinarith [mul_nonneg hh (sq_nonneg (f s))]

structure Projection where
  op : (((I → Ω) → ℝ) →ₗ[ℝ] ((I → Ω) → ℝ))
  idem : ∀ f, op (op f) = op f
  adj : ∀ f g, dot p (op f) g = dot p f (op g)

namespace Projection

variable {p}

noncomputable def identity : Projection p where
  op := LinearMap.id
  idem _ := rfl
  adj _ _ := rfl

noncomputable def complement (P : Projection p) : Projection p where
  op := LinearMap.id - P.op
  idem f := by
    change f-P.op f-P.op (f-P.op f) = f-P.op f
    rw [map_sub, P.idem]
    abel
  adj f g := by
    change dot p (f-P.op f) g = dot p f (g-P.op g)
    rw [dot_sub_left, dot_sub_right, P.adj]

noncomputable def comp (P Q : Projection p)
    (hc : ∀ f, P.op (Q.op f) = Q.op (P.op f)) : Projection p where
  op := P.op.comp Q.op
  idem f := by
    change P.op (Q.op (P.op (Q.op f))) = P.op (Q.op f)
    rw [← hc, Q.idem, P.idem]
  adj f g := by
    change dot p (P.op (Q.op f)) g = dot p f (P.op (Q.op g))
    rw [P.adj, Q.adj, hc]

lemma dot_image (P : Projection p) (f : (I → Ω) → ℝ) :
    dot p f (P.op f) = dot p (P.op f) (P.op f) := by
  rw [P.adj, P.idem]

end Projection

noncomputable def avgProjection (hp : ∀ i, ∑ a, p i a = 1) (i : I) : Projection p where
  op := average p i
  idem := average_idem p hp i
  adj := average_adjoint p i

noncomputable def avgList : List I → (((I → Ω) → ℝ) →ₗ[ℝ] ((I → Ω) → ℝ))
  | [] => LinearMap.id
  | i::l => (average p i).comp (avgList l)

omit [Fintype I] in
lemma avgList_nil (f : (I → Ω) → ℝ) : avgList p [] f = f := rfl

omit [Fintype I] in
lemma avgList_cons (i : I) (l : List I) (f : (I → Ω) → ℝ) :
    avgList p (i::l) f = average p i (avgList p l f) := rfl

omit [Fintype I] in
lemma average_comm_list (i : I) (l : List I) (f : (I → Ω) → ℝ) :
    average p i (avgList p l f) = avgList p l (average p i f) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [avgList_cons, average_comm, ih, avgList_cons]

omit [Fintype I] in
lemma avgList_idem (hp : ∀ i, ∑ a, p i a = 1) (l : List I) (f : (I → Ω) → ℝ) :
    avgList p l (avgList p l f) = avgList p l f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [avgList_cons]
    rw [← average_comm_list, ih, average_idem p hp]

lemma avgList_adjoint (l : List I) (f g : (I → Ω) → ℝ) :
    dot p (avgList p l f) g = dot p f (avgList p l g) := by
  induction l generalizing g with
  | nil => rfl
  | cons i l ih =>
    rw [avgList_cons, average_adjoint, ih, ← average_comm_list, avgList_cons]

noncomputable def listProjection (hp : ∀ i, ∑ a, p i a = 1) (l : List I) : Projection p where
  op := avgList p l
  idem := avgList_idem p hp l
  adj := avgList_adjoint p l

omit [Fintype I] in
lemma average_list_mem (hp : ∀ i, ∑ a, p i a = 1) (l : List I) (i : I) (hi : i ∈ l)
    (f : (I → Ω) → ℝ) : average p i (avgList p l f) = avgList p l f := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · simpa only [avgList_cons] using average_idem p hp i (avgList p l f)
    · rw [avgList_cons, average_comm, ih hi]

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω]

variable (p : I → Ω → ℝ)

noncomputable def outside (x y : I) : List I :=
  (Finset.univ.filter (fun i => x < i ∧ i ≠ y)).toList

noncomputable def pairCondition (x y : I) :
    (((I → Ω) → ℝ) →ₗ[ℝ] ((I → Ω) → ℝ)) := avgList p (outside x y)

noncomputable def residual (x y : I) :
    (((I → Ω) → ℝ) →ₗ[ℝ] ((I → Ω) → ℝ)) :=
  (LinearMap.id-average p x).comp
    ((LinearMap.id-average p y).comp (pairCondition p x y))

lemma residual_apply (x y : I) (f : (I → Ω) → ℝ) :
    residual p x y f =
      pairCondition p x y f - average p y (pairCondition p x y f) -
        average p x (pairCondition p x y f - average p y (pairCondition p x y f)) := rfl

lemma residual_formula (x y : I) (f : (I → Ω) → ℝ) :
    residual p x y f = pairCondition p x y f -
      average p x (pairCondition p x y f) - average p y (pairCondition p x y f) +
      average p x (average p y (pairCondition p x y f)) := by
  rw [residual_apply, map_sub]; abel

lemma average_condition_comm (i x y : I) (f : (I → Ω) → ℝ) :
    average p i (pairCondition p x y f) = pairCondition p x y (average p i f) :=
  average_comm_list p i (outside x y) f

lemma average_residual_comm (i x y : I) (f : (I → Ω) → ℝ) :
    average p i (residual p x y f) = residual p x y (average p i f) := by
  simp only [residual_apply, map_sub]
  simp_rw [average_comm p i x, average_comm p i y, average_condition_comm p i x y]

lemma residual_center_x (hp : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    average p x (residual p x y f) = 0 := by
  rw [residual_apply, map_sub, average_idem p hp, sub_self]

lemma residual_center_y (hp : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    average p y (residual p x y f) = 0 := by
  simp only [residual_apply, map_sub]
  rw [average_idem p hp, average_comm p y x, average_comm p y x,
    average_idem p hp]
  simp

lemma condition_invariant (hp : ∀ i, ∑ a, p i a = 1) (i x y : I)
    (hix : x < i) (hiy : i ≠ y) (f : (I → Ω) → ℝ) :
    average p i (pairCondition p x y f) = pairCondition p x y f := by
  apply average_list_mem p hp
  simp [outside, hix, hiy]

lemma residual_invariant (hp : ∀ i, ∑ a, p i a = 1) (i x y : I)
    (hix : x < i) (hiy : i ≠ y) (f : (I → Ω) → ℝ) :
    average p i (residual p x y f) = residual p x y f := by
  simp only [residual_apply, map_sub]
  simp_rw [average_comm p i x, average_comm p i y,
    condition_invariant p hp i x y hix hiy]

lemma residual_projection (hp : ∀ i, ∑ a, p i a = 1) (x y : I) :
    ∃ P : Projection p, P.op = residual p x y := by
  let X := (avgProjection p hp x).complement
  let Y := (avgProjection p hp y).complement
  let C := listProjection p hp (outside x y)
  have hyc : ∀ f, Y.op (C.op f) = C.op (Y.op f) := by
    intro f
    change pairCondition p x y f-average p y (pairCondition p x y f) =
      pairCondition p x y (f-average p y f)
    rw [map_sub, average_condition_comm]
  have hxc : ∀ f, X.op ((Y.comp C hyc).op f) = (Y.comp C hyc).op (X.op f) := by
    intro f
    change (pairCondition p x y f-average p y (pairCondition p x y f)) -
      average p x (pairCondition p x y f-average p y (pairCondition p x y f)) =
      pairCondition p x y (f-average p x f) -
        average p y (pairCondition p x y (f-average p x f))
    simp only [map_sub]
    rw [← average_condition_comm, average_comm p x y]
    abel
  exact ⟨X.comp (Y.comp C hyc) hxc, rfl⟩

lemma residual_dot (hp : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    dot p f (residual p x y f) = dot p (residual p x y f) (residual p x y f) := by
  obtain ⟨P,hP⟩ := residual_projection p hp x y
  rw [← hP]
  exact P.dot_image f

omit [LinearOrder I] in
lemma centered_invariant_orthogonal (i : I) (f g : (I → Ω) → ℝ)
    (hf : average p i f = 0) (hg : average p i g = g) : dot p f g = 0 := by
  rw [← hg, ← average_adjoint, hf, dot_zero_left]

lemma residual_orthogonal (hp : ∀ i, ∑ a, p i a = 1) (x y u v : I)
    (hxy : x < y) (huv : u < v) (hd : (x,y) ≠ (u,v)) (f : (I → Ω) → ℝ) :
    dot p (residual p x y f) (residual p u v f) = 0 := by
  rcases lt_trichotomy y v with hyv | rfl | hvy
  · rw [dot_comm]
    exact centered_invariant_orthogonal p v _ _ (residual_center_y p hp u v f)
      (residual_invariant p hp v x y (lt_trans hxy hyv) (ne_of_gt hyv) f)
  · rcases lt_trichotomy x u with hxu | rfl | hux
    · rw [dot_comm]
      exact centered_invariant_orthogonal p u _ _ (residual_center_x p hp u y f)
        (residual_invariant p hp u x y hxu (ne_of_lt huv) f)
    · exact (hd rfl).elim
    · exact centered_invariant_orthogonal p x _ _ (residual_center_x p hp x y f)
        (residual_invariant p hp x u y hux (ne_of_lt hxy) f)
  · exact centered_invariant_orthogonal p y _ _ (residual_center_y p hp x y f)
      (residual_invariant p hp y u v (lt_trans huv hvy) (ne_of_gt hvy) f)

omit [Fintype I] [LinearOrder I] in
lemma average_one (hp : ∀ i, ∑ a, p i a = 1) (i : I) :
    average p i (fun _ => 1) = (fun _ => 1) := by
  funext s; simpa [average_apply] using hp i

lemma residual_mean_zero (hp : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    dot p (fun _ => 1) (residual p x y f) = 0 := by
  rw [dot_comm]
  exact centered_invariant_orthogonal p x _ _ (residual_center_x p hp x y f)
    (average_one p hp x)

end

section

open Finset

variable {I Ω J : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

variable (p : I → Ω → ℝ)

lemma dot_sum_right (S : Finset J) (f : (I → Ω) → ℝ) (r : J → (I → Ω) → ℝ) :
    dot p f (∑ j ∈ S, r j) = ∑ j ∈ S, dot p f (r j) := by
  unfold dot
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma dot_sum_left (S : Finset J) (r : J → (I → Ω) → ℝ) (f : (I → Ω) → ℝ) :
    dot p (∑ j ∈ S, r j) f = ∑ j ∈ S, dot p (r j) f := by
  rw [dot_comm, dot_sum_right]
  exact Finset.sum_congr rfl (fun j _ => dot_comm p f (r j))

end

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω]

theorem residual_sum (p : I → Ω → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hs : ∀ i, ∑ a, p i a = 1) (pairs : Finset (I × I))
    (hpair : ∀ z ∈ pairs, z.1 < z.2) (f : (I → Ω) → ℝ) :
    (∑ z ∈ pairs, dot p (residual p z.1 z.2 f) (residual p z.1 z.2 f)) ≤
      ∑ s, density p s * (f s - ∑ t, density p t * f t)^2 := by
  classical
  let r : (I × I) → (I → Ω) → ℝ := fun z => residual p z.1 z.2 f
  let R := ∑ z ∈ pairs, r z
  let m := ∑ t, density p t * f t
  let F := f - (fun _ => m)
  have hd (z) : dot p F (r z) = dot p (r z) (r z) := by
    change dot p (f-(fun _ => m)) (residual p z.1 z.2 f) = _
    rw [dot_sub_left, dot_const_left, residual_mean_zero p hs, mul_zero, sub_zero]
    exact residual_dot p hs z.1 z.2 f
  have hFR : dot p F R = ∑ z ∈ pairs, dot p (r z) (r z) := by
    rw [dot_sum_right]
    exact Finset.sum_congr rfl (fun z _ => hd z)
  have hRR : dot p R R = ∑ z ∈ pairs, dot p (r z) (r z) := by
    rw [dot_sum_left]
    apply Finset.sum_congr rfl
    intro z hz
    rw [dot_sum_right]
    apply Finset.sum_eq_single z
    · intro w hw hwz
      apply residual_orthogonal p hs z.1 z.2 w.1 w.2 (hpair z hz) (hpair w hw)
      simpa only [Prod.mk.eta] using Ne.symm hwz
    · exact fun hn => (hn hz).elim
  have hn := dot_nonneg p hp (F-R)
  rw [dot_sub_left p F R (F-R), dot_sub_right p F F R,
    dot_sub_right p R F R, dot_comm p R F, hFR, hRR] at hn
  have hff : dot p F F = ∑ s, density p s * (f s-∑ t, density p t*f t)^2 := by
    unfold dot
    apply Finset.sum_congr rfl
    intro s _
    change density p s * (f s-m) * (f s-m) = density p s * (f s-m)^2
    ring
  rw [← hff]
  change (∑ z ∈ pairs, dot p (r z) (r z)) ≤ dot p F F
  linarith

end MatchingFPRAS.Replica

end OAI
