import OAI.Geometry.UnitDistances.Basic

namespace OAI

namespace PlanarUnitDistances.CircleCutting
open Set Polynomial

abbrev Plane := EuclideanSpace ℝ (Fin 2)

lemma plane_dist_sq (p q : Plane) :
    dist p q ^ 2 = (p 0-q 0)^2+(p 1-q 1)^2 := by
  rw [dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  simp only [WithLp.ofLp_sub,Pi.sub_apply,Real.norm_eq_abs,sq_abs]

lemma finite_circle_intersection (c d : Plane) (hcd : c ≠ d) :
    {p : Plane | dist p c = 1 ∧ dist p d = 1}.Finite := by
  let S : Set Plane := {p | dist p c = 1 ∧ dist p d = 1}
  by_cases hs : S.Subsingleton
  · exact hs.finite
  obtain ⟨a,ha,b,hb,hab⟩ := Set.not_subsingleton_iff.mp hs
  apply (Set.toFinite ({a,b} : Set Plane)).subset
  intro p hp
  apply Set.mem_insert_iff.mpr
  have h := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (by simp : Module.finrank ℝ Plane = 2) hcd hab ha.1 hb.1 hp.1 ha.2 hb.2 hp.2
  exact h.imp_right (fun h => Set.mem_singleton_iff.mpr h)

noncomputable def circleIntersections (Q : Finset Plane) : Finset Plane := by
  classical
  exact ((Q ×ˢ Q).biUnion fun cd => if h : cd.1 = cd.2 then ∅ else
    (finite_circle_intersection cd.1 cd.2 h).toFinset)

lemma mem_circleIntersections {Q : Finset Plane} {c d p : Plane}
    (hc : c ∈ Q) (hd : d ∈ Q) (hcd : c ≠ d)
    (hpc : dist p c = 1) (hpd : dist p d = 1) : p ∈ circleIntersections Q := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨(c,d),Finset.mem_product.mpr ⟨hc,hd⟩,?_⟩
  simp only [dite_eq_right hcd,Set.Finite.mem_toFinset,mem_ofPred_eq]
  exact ⟨hpc,hpd⟩

noncomputable def direction (t : ℝ) : Plane :=
  WithLp.toLp 2 ![(1-t^2)/(1+t^2), 2*t/(1+t^2)]

lemma direction_unit (t : ℝ) : (direction t 0)^2+(direction t 1)^2 = 1 := by
  have ht : 1+t^2 ≠ 0 := by nlinarith [sq_nonneg t]
  simp only [direction,WithLp.ofLp_toLp,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp
  ring

noncomputable def projection (e p : Plane) : ℝ := e 0*p 0+e 1*p 1

noncomputable def directionPolynomial (a b c : ℝ) : Polynomial ℝ :=
  C a*(1-X^2)+C b*(2*X)-C c*(1+X^2)

lemma directionPolynomial_ne_zero {a b c : ℝ} (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    directionPolynomial a b c ≠ 0 := by
  intro hz
  have h0 := congrArg (fun p : Polynomial ℝ => p.coeff 0) hz
  have h1 := congrArg (fun p : Polynomial ℝ => p.coeff 1) hz
  have h2 := congrArg (fun p : Polynomial ℝ => p.coeff 2) hz
  norm_num [directionPolynomial, coeff_one, coeff_X] at h0 h1 h2
  rcases h with h | h | h <;> apply h <;> linarith

lemma directionPolynomial_eval (a b c t : ℝ) :
    (directionPolynomial a b c).eval t =
      (direction t 0*a+direction t 1*b-c)*(1+t^2) := by
  have ht : 1+t^2 ≠ 0 := by nlinarith [sq_nonneg t]
  simp only [directionPolynomial,eval_sub,eval_add,eval_mul,eval_C,eval_one,eval_pow,
    eval_X,Polynomial.eval_ofNat,direction,WithLp.ofLp_toLp,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  field_simp

lemma avoids_finite_polynomials {ι : Type*} [Finite ι]
    (f : ι → Polynomial ℝ) (hf : ∀ i, f i ≠ 0) :
    ∃ t : ℝ, ∀ i, (f i).eval t ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  let F := ∏ i, f i
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)
  have he : ∃ t, F.eval t ≠ 0 := by
    by_contra h
    push Not at h
    exact hF (Polynomial.zero_of_eval_zero F h)
  obtain ⟨t,ht⟩ := he
  refine ⟨t,fun i hi => ht ?_⟩
  simp only [F,eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem exists_good_direction (A P Q : Finset Plane) :
    ∃ e : Plane, (e 0)^2+(e 1)^2 = 1 ∧
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → projection e a ≠ projection e b) ∧
      (∀ p ∈ P, ∀ c ∈ Q, projection e (p-c) ≠ 1 ∧ projection e (p-c) ≠ -1) := by
  classical
  let I := {ab : A × A // ab.1 ≠ ab.2}
  let J := P × Q × Bool
  let f : I ⊕ J → Polynomial ℝ := fun k => match k with
    | .inl ab => directionPolynomial ((ab.val.1 : Plane) 0-(ab.val.2 : Plane) 0)
        ((ab.val.1 : Plane) 1-(ab.val.2 : Plane) 1) 0
    | .inr pc => directionPolynomial ((pc.1 : Plane) 0-(pc.2.1 : Plane) 0)
        ((pc.1 : Plane) 1-(pc.2.1 : Plane) 1) (if pc.2.2 then 1 else -1)
  have hf : ∀ k, f k ≠ 0 := by
    intro k
    cases k with
    | inl ab =>
      apply directionPolynomial_ne_zero
      by_contra h
      push Not at h
      apply ab.property
      apply Subtype.ext
      ext i
      fin_cases i
      · exact sub_eq_zero.mp h.1
      · exact sub_eq_zero.mp h.2.1
    | inr pc =>
      apply directionPolynomial_ne_zero
      right; right
      split <;> norm_num
  obtain ⟨t,ht⟩ := avoids_finite_polynomials f hf
  refine ⟨direction t,direction_unit t,?_,?_⟩
  · intro a ha b hb hab heq
    have hne := ht (.inl ⟨(⟨a,ha⟩,⟨b,hb⟩),by intro h; exact hab (congrArg Subtype.val h)⟩)
    apply hne
    rw [show f (.inl ⟨(⟨a,ha⟩,⟨b,hb⟩),_⟩) = directionPolynomial (a 0-b 0) (a 1-b 1) 0 from rfl,
      directionPolynomial_eval]
    unfold projection at heq
    have hz : direction t 0*(a 0-b 0)+direction t 1*(a 1-b 1)-0 = 0 := by linarith
    rw [hz,zero_mul]
  · intro p hp c hc
    constructor
    · intro heq
      have hne := ht (.inr (⟨p,hp⟩,⟨c,hc⟩,true))
      apply hne
      change (directionPolynomial (p 0-c 0) (p 1-c 1) 1).eval t = 0
      rw [directionPolynomial_eval]
      change direction t 0*(p 0-c 0)+direction t 1*(p 1-c 1) = 1 at heq
      rw [heq,sub_self,zero_mul]
    · intro heq
      have hne := ht (.inr (⟨p,hp⟩,⟨c,hc⟩,false))
      apply hne
      change (directionPolynomial (p 0-c 0) (p 1-c 1) (-1)).eval t = 0
      rw [directionPolynomial_eval]
      change direction t 0*(p 0-c 0)+direction t 1*(p 1-c 1) = -1 at heq
      rw [heq,sub_self,zero_mul]

noncomputable def rotate (e p : Plane) : Plane :=
  WithLp.toLp 2 ![projection e p,-e 1*p 0+e 0*p 1]

lemma rotate_dist (e : Plane) (he : (e 0)^2+(e 1)^2=1) (p q : Plane) :
    dist (rotate e p) (rotate e q) = dist p q := by
  apply (sq_eq_sq₀ (dist_nonneg) (dist_nonneg)).mp
  rw [plane_dist_sq,plane_dist_sq]
  simp only [rotate,projection,WithLp.ofLp_toLp,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  nlinarith [sq_nonneg (p 0-q 0),sq_nonneg (p 1-q 1)]

lemma continuous_rotate (e : Plane) : Continuous (rotate e) := by
  unfold rotate projection
  fun_prop

lemma rotate_injective (e : Plane) (he : (e 0)^2+(e 1)^2=1) :
    Function.Injective (rotate e) := by
  intro p q h
  apply dist_eq_zero.mp
  rw [← rotate_dist e he,h,dist_self]

lemma circle_intersection_card (c d : Plane) (hcd : c ≠ d) (S : Finset Plane)
    (hS : ∀ p ∈ S, dist p c=1 ∧ dist p d=1) : S.card ≤ 2 := by
  classical
  by_cases hs : (S : Set Plane).Subsingleton
  · exact (Finset.card_le_one.mpr (fun a ha b hb => hs ha hb)).trans (by decide)
  obtain ⟨a,ha,b,hb,hab⟩ := Set.not_subsingleton_iff.mp hs
  apply (Finset.card_le_card (show S ⊆ {a,b} from ?_)).trans Finset.card_le_two
  intro p hp
  have h := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (by simp : Module.finrank ℝ Plane = 2) hcd hab
    (hS a ha).1 (hS b hb).1 (hS p hp).1
    (hS a ha).2 (hS b hb).2 (hS p hp).2
  simpa only [Finset.mem_insert,Finset.mem_singleton] using h

lemma circleIntersections_card (Q : Finset Plane) :
    (circleIntersections Q).card ≤ 2*Q.card^2 := by
  classical
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun cd _ => show
      (if h : cd.1=cd.2 then ∅ else (finite_circle_intersection cd.1 cd.2 h).toFinset).card ≤ 2 from ?_)).trans
  · simp [Finset.card_product,pow_two,mul_comm]
  · split
    · simp
    · apply circle_intersection_card
      · assumption
      · intro p hp
        simpa only [Set.Finite.mem_toFinset,mem_ofPred_eq] using hp

noncomputable def branch (c : Plane) (upper : Bool) (x : ℝ) : ℝ :=
  c 1 + if upper then Real.sqrt (1-(x-c 0)^2) else -Real.sqrt (1-(x-c 0)^2)

def active (c : Plane) (x : ℝ) : Prop := c 0-1 < x ∧ x < c 0+1

lemma active_radicand {c : Plane} {x : ℝ} (h : active c x) :
    0 < 1-(x-c 0)^2 := by
  unfold active at h
  nlinarith

lemma closed_radicand {c : Plane} {x : ℝ} (h : c 0-1 ≤ x ∧ x ≤ c 0+1) :
    0 ≤ 1-(x-c 0)^2 := by
  nlinarith

lemma continuous_branch (c : Plane) (b : Bool) : Continuous (branch c b) := by
  cases b <;> unfold branch <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop

lemma branch_order {c : Plane} {x : ℝ} (h : active c x) :
    branch c false x < branch c true x := by
  have hs := Real.sqrt_pos.mpr (active_radicand h)
  simp only [branch,Bool.false_eq_true,ite_false,ite_true]
  linarith

noncomputable def graphPoint (c : Plane) (b : Bool) (x : ℝ) : Plane :=
  WithLp.toLp 2 ![x,branch c b x]

lemma graphPoint_unit {c : Plane} {x : ℝ} (b : Bool)
    (h : c 0-1 ≤ x ∧ x ≤ c 0+1) : dist (graphPoint c b x) c = 1 := by
  have hs := Real.sq_sqrt (closed_radicand h)
  have hd := plane_dist_sq (graphPoint c b x) c
  apply (sq_eq_sq₀ dist_nonneg (by positivity : (0:ℝ) ≤ 1)).mp
  rw [hd]
  cases b <;> simp only [graphPoint,branch,WithLp.ofLp_toLp,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,Bool.false_eq_true,ite_false,ite_true]
  all_goals nlinarith

lemma unit_iff_graph {c p : Plane} (h : active c (p 0)) :
    dist p c = 1 ↔ ∃ b : Bool, p 1=branch c b (p 0) := by
  constructor
  · intro hp
    have hd := plane_dist_sq p c
    have hs := Real.sq_sqrt (le_of_lt (active_radicand h))
    rw [hp] at hd
    have he : (p 1-c 1)^2 = (Real.sqrt (1-(p 0-c 0)^2))^2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with hg | hg
    · refine ⟨true,?_⟩
      simp only [branch,ite_true]; linarith
    · refine ⟨false,?_⟩
      simp only [branch,Bool.false_eq_true,ite_false]; linarith
  · rintro ⟨b,hb⟩
    have hp : p = graphPoint c b (p 0) := by
      ext i
      fin_cases i
      · rfl
      · exact hb
    rw [hp]
    exact graphPoint_unit b ⟨le_of_lt h.1,le_of_lt h.2⟩

lemma unit_projection_closed {c p : Plane} (h : dist p c=1) :
    c 0-1 ≤ p 0 ∧ p 0 ≤ c 0+1 := by
  have hd := plane_dist_sq p c
  rw [h] at hd
  constructor <;> nlinarith [sq_nonneg (p 1-c 1)]

lemma active_of_unit_nonextreme {c p : Plane} (h : dist p c=1)
    (hlo : p 0 ≠ c 0-1) (hhi : p 0 ≠ c 0+1) : active c (p 0) :=
  ⟨lt_of_le_of_ne (unit_projection_closed h).1 (Ne.symm hlo),
    lt_of_le_of_ne (unit_projection_closed h).2 hhi⟩

noncomputable def eventAbscissas (Q : Finset Plane) : Finset ℝ :=
  (Q.biUnion fun c => {c 0-1,c 0+1}) ∪ (circleIntersections Q).image (· 0)

lemma extrema_mem_events {Q : Finset Plane} {c : Plane} (hc : c ∈ Q) :
    c 0-1 ∈ eventAbscissas Q ∧ c 0+1 ∈ eventAbscissas Q := by
  classical
  constructor <;> apply Finset.mem_union_left <;>
    apply Finset.mem_biUnion.mpr <;> refine ⟨c,hc,?_⟩ <;> simp

lemma branch_collision_event {Q : Finset Plane} {c d : Plane}
    (hc : c ∈ Q) (hd : d ∈ Q) {b b' : Bool} {x : ℝ}
    (hx : active c x) (hx' : active d x)
    (hne : (c,b) ≠ (d,b')) (he : branch c b x=branch d b' x) :
    x ∈ eventAbscissas Q := by
  classical
  have hcd : c ≠ d := by
    rintro rfl
    have hbb : b ≠ b' := fun h => hne (by rw [h])
    cases b <;> cases b' <;> simp only [ne_eq,not_true_eq_false] at hbb
    · exact (ne_of_lt (branch_order hx)) he
    · exact (ne_of_gt (branch_order hx)) he
  have hp : graphPoint c b x=graphPoint d b' x := by
    ext i
    fin_cases i
    · rfl
    · exact he
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨graphPoint c b x,?_,rfl⟩
  apply mem_circleIntersections hc hd hcd (graphPoint_unit b ⟨hx.1.le,hx.2.le⟩)
  rw [hp]
  exact graphPoint_unit b' ⟨hx'.1.le,hx'.2.le⟩

lemma same_side_of_not_mem {S : Set ℝ} (hS : S.OrdConnected)
    {a x y : ℝ} (ha : a ∉ S) (hx : x ∈ S) (hy : y ∈ S) :
    (a < x ↔ a < y) ∧ (x < a ↔ y < a) := by
  constructor <;> constructor <;> intro h
  · by_contra hn
    exact ha (hS.out hy hx ⟨le_of_not_gt hn,h.le⟩)
  · by_contra hn
    exact ha (hS.out hx hy ⟨le_of_not_gt hn,h.le⟩)
  · by_contra hn
    exact ha (hS.out hx hy ⟨h.le,le_of_not_gt hn⟩)
  · by_contra hn
    exact ha (hS.out hy hx ⟨h.le,le_of_not_gt hn⟩)

lemma active_constant {Q : Finset Plane} {S : Set ℝ} (hS : S.OrdConnected)
    (hE : ∀ x ∈ S, x ∉ eventAbscissas Q) {c : Plane} (hc : c ∈ Q)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : active c x ↔ active c y := by
  have hlo : c 0-1 ∉ S := fun h => hE _ h (extrema_mem_events hc).1
  have hhi : c 0+1 ∉ S := fun h => hE _ h (extrema_mem_events hc).2
  exact and_congr (same_side_of_not_mem hS hlo hx hy).1
    (same_side_of_not_mem hS hhi hx hy).2

lemma order_constant {S : Set ℝ} (hS : S.OrdConnected) {f g : ℝ → ℝ}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hne : ∀ x ∈ S, f x ≠ g x) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : f x < g x) : f y < g y := by
  by_contra hn
  obtain ⟨z,hz,he⟩ := hS.isPreconnected.intermediate_value hx hy (hf.sub hg)
    (show (0:ℝ) ∈ Set.Icc (f x-g x) (f y-g y) from ⟨sub_nonpos.mpr hxy.le,
      sub_nonneg.mpr (le_of_not_gt hn)⟩)
  exact hne z hz (sub_eq_zero.mp he)

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.Sweep
open Finset Classical

variable {α : Type*} [DecidableEq α]

lemma sdiff_triangle (A B C : Finset α) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  apply (card_le_card (show A \ C ⊆ (A \ B) ∪ (B \ C) from ?_)).trans
    (card_union_le _ _)
  intro a ha
  simp only [mem_sdiff,mem_union] at *
  by_cases h : a ∈ B
  · exact Or.inr ⟨h,ha.2⟩
  · exact Or.inl ⟨ha.1,h⟩

lemma sdiff_insert_same (a : α) (A B : Finset α) :
    (insert a A \ insert a B).card ≤ (A \ B).card := by
  apply card_le_card
  intro x hx
  simp only [mem_sdiff,mem_insert] at *
  exact ⟨hx.1.resolve_left (fun h => hx.2 (Or.inl h)),fun h => hx.2 (Or.inr h)⟩

lemma sdiff_insert_left (a : α) (A B : Finset α) :
    (insert a A \ B).card ≤ 1 + (A \ B).card := by
  apply (card_le_card (show insert a A \ B ⊆ insert a (A \ B) from ?_)).trans
  · exact (card_insert_le _ _).trans_eq (Nat.add_comm _ _)
  · intro x hx
    simp only [mem_sdiff,mem_insert] at *
    exact hx.1.elim Or.inl (fun h => Or.inr ⟨h,hx.2⟩)

lemma sdiff_insert_right (a : α) (A B : Finset α) :
    (A \ insert a B).card ≤ (A \ B).card :=
  card_le_card (sdiff_subset_sdiff (Subset.refl _) (subset_insert _ _))

def links (x : Option α) : List α → Finset (Option α × Option α)
  | [] => {(x,none)}
  | a::L => insert (x,some a) (links (some a) L)

def gaps (L : List α) : Finset (Option α × Option α) := links none L

lemma links_card_le (x : Option α) (L : List α) :
    (links x L).card ≤ L.length+1 := by
  induction L generalizing x with
  | nil => simp [links]
  | cons a L ih =>
    apply (card_insert_le _ _).trans
    simpa only [List.length_cons] using Nat.add_le_add_right (ih (some a)) 1

lemma links_change_start (x y : Option α) (L : List α) :
    (links x L \ links y L).card ≤ 1 := by
  cases L with
  | nil => exact (card_le_card sdiff_subset).trans (by simp [links])
  | cons a L =>
    apply (sdiff_insert_left _ _ _).trans
    have h : links (some a) L \ insert (y,some a) (links (some a) L) = ∅ :=
      sdiff_eq_empty_iff_subset.mpr (subset_insert _ _)
    simp only [links,h,card_empty,add_zero,le_refl]

lemma links_delete_head (x : Option α) (a : α) (L : List α) :
    (links x (a::L) \ links x L).card ≤ 2 ∧
      (links x L \ links x (a::L)).card ≤ 1 := by
  constructor
  · exact (sdiff_insert_left _ _ _).trans (by
      have h := links_change_start (some a) x L
      omega)
  · exact (sdiff_insert_right _ _ _).trans (links_change_start x (some a) L)

theorem links_filter_sdiff (C : Finset α) (x : Option α) (L : List α) :
    (links x L \ links x (L.filter (· ∉ C))).card ≤ 2*(L.filter (· ∈ C)).length ∧
    (links x (L.filter (· ∉ C)) \ links x L).card ≤ (L.filter (· ∈ C)).length := by
  induction L generalizing x with
  | nil => simp [links]
  | cons a L ih =>
    by_cases ha : a ∈ C
    · simp only [List.filter_cons]
      simp only [ha,not_true_eq_false,decide_true,decide_false,
        Bool.false_eq_true,ite_true,ite_false,List.length_cons]
      have h := ih x
      have hd := links_delete_head x a L
      constructor
      · have ht := sdiff_triangle (links x (a::L)) (links x L)
          (links x (L.filter (· ∉ C)))
        omega
      · have ht := sdiff_triangle (links x (L.filter (· ∉ C))) (links x L)
          (links x (a::L))
        omega
    · simp only [List.filter_cons]
      simp only [ha,not_false_eq_true,decide_true,decide_false,
        Bool.false_eq_true,ite_true,ite_false]
      constructor
      · exact (sdiff_insert_same _ _ _).trans (ih (some a)).1
      · exact (sdiff_insert_same _ _ _).trans (ih (some a)).2

def touches (C : Finset α) (g : Option α × Option α) : Prop :=
  (∃ a ∈ C, g.1 = some a) ∨ (∃ a ∈ C, g.2 = some a)

lemma links_touch_card (C : Finset α) (x : Option α) (L : List α) :
    ((links x L).filter (touches C)).card ≤
      2*(L.filter (· ∈ C)).length + if ∃ a ∈ C, x = some a then 1 else 0 := by
  classical
  induction L generalizing x with
  | nil =>
    have ht : touches C (x,none) ↔ ∃ a ∈ C, x = some a := by simp [touches]
    by_cases hx : ∃ a ∈ C, x = some a
    · simpa only [links,List.filter_nil,List.length_nil,mul_zero,zero_add,ite_eq_left hx]
        using (card_filter_le (s := ({(x,none)} : Finset (Option α × Option α)))
          (p := touches C)).trans_eq (card_singleton _)
    · have hno : ¬touches C (x,none) := mt ht.mp hx
      simp [links,hx,hno]
  | cons a L ih =>
    have ht : touches C (x,some a) ↔ (∃ b ∈ C, x = some b) ∨ a ∈ C := by
      simp [touches]
    have htail := ih (some a)
    by_cases ha : a ∈ C
    · have hhead : touches C (x,some a) := ht.mpr (Or.inr ha)
      rw [links,filter_insert,ite_eq_left hhead]
      apply (card_insert_le _ _).trans
      simp [ha] at htail ⊢
      split <;> omega
    · simp [ha] at htail
      by_cases hx : ∃ b ∈ C, x = some b
      · rw [links,filter_insert,ite_eq_left (ht.mpr (Or.inl hx))]
        apply (card_insert_le _ _).trans
        simp [ha,hx]
        omega
      · rw [links,filter_insert,ite_eq_right (by simp only [ht,hx,ha,or_self,not_false_eq_true])]
        simpa [ha,hx] using htail

theorem event_starts_card (C : Finset α) (L R : List α)
    (hL : L.Nodup) (hR : R.Nodup)
    (hskel : L.filter (· ∉ C) = R.filter (· ∉ C)) :
    ((gaps R).filter (fun g => g ∉ gaps L ∨ touches C g)).card ≤ 5*C.card := by
  classical
  have hleft : (L.filter (· ∈ C)).length ≤ C.card := by
    rw [← List.toFinset_card_of_nodup (hL.filter _)]
    exact card_le_card (by intro a ha; exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp ha)).2)
  have hright : (R.filter (· ∈ C)).length ≤ C.card := by
    rw [← List.toFinset_card_of_nodup (hR.filter _)]
    exact card_le_card (by intro a ha; exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp ha)).2)
  have hd : (gaps R \ gaps L).card ≤ 3*C.card := by
    have ht := sdiff_triangle (gaps R) (gaps (L.filter (· ∉ C))) (gaps L)
    have h1 := (links_filter_sdiff C none R).1
    have h2 := (links_filter_sdiff C none L).2
    change (gaps (L.filter (· ∉ C)) \ gaps L).card ≤ _ at h2
    change (gaps R \ gaps (R.filter (· ∉ C))).card ≤ _ at h1
    rw [← hskel] at h1
    omega
  have hb : ((gaps R).filter (touches C)).card ≤ 2*C.card := by
    have h := links_touch_card C none R
    simp at h
    exact h.trans (Nat.mul_le_mul_left _ hright)
  apply (card_le_card (show (gaps R).filter (fun g => g ∉ gaps L ∨ touches C g) ⊆
      (gaps R \ gaps L) ∪ (gaps R).filter (touches C) from ?_)).trans
      (card_union_le _ _) |>.trans (by omega)
  intro g hg
  simp only [mem_filter,mem_sdiff,mem_union] at *
  exact hg.2.elim (fun h => Or.inl ⟨hg.1,h⟩) (fun h => Or.inr ⟨hg.1,h⟩)

end PlanarUnitDistances.Sweep

namespace PlanarUnitDistances.SweepIntervals
open Finset Set Classical

lemma between_finsets (A B : Finset ℝ) (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    ∃ x : ℝ, (∀ a ∈ A, a < x) ∧ (∀ b ∈ B, x < b) := by
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · obtain ⟨x,hx1,hx2⟩ := exists_between (h _ (A.max'_mem hA) _ (B.min'_mem hB))
      exact ⟨x,fun a ha => (A.le_max' a ha).trans_lt hx1,
        fun b hb => hx2.trans_le (B.min'_le b hb)⟩
    · refine ⟨A.max' hA+1,fun a ha => (A.le_max' a ha).trans_lt (by linarith),?_⟩
      exact fun b hb => False.elim (hB ⟨b,hb⟩)
  · by_cases hB : B.Nonempty
    · refine ⟨B.min' hB-1,?_,fun b hb => (show B.min' hB-1 < B.min' hB by linarith).trans_le (B.min'_le b hb)⟩
      exact fun a ha => False.elim (hA ⟨a,ha⟩)
    · exact ⟨0,fun a ha => False.elim (hA ⟨a,ha⟩),
        fun b hb => False.elim (hB ⟨b,hb⟩)⟩

def span {n : ℕ} (a : Fin n → ℝ) (lo hi : ℕ) : Set ℝ :=
  {x | (∀ i, i.val < lo → a i < x) ∧ (∀ i, hi ≤ i.val → x < a i)}

abbrev slab {n : ℕ} (a : Fin n → ℝ) (k : ℕ) := span a k k

lemma span_ordConnected {n : ℕ} (a : Fin n → ℝ) (lo hi : ℕ) :
    (span a lo hi).OrdConnected := by
  constructor
  intro x hx y hy z hz
  exact ⟨fun i hi => (hx.1 i hi).trans_le hz.1,
    fun i hi => hz.2.trans_lt (hy.2 i hi)⟩

lemma span_open {n : ℕ} (a : Fin n → ℝ) (lo hi : ℕ) : IsOpen (span a lo hi) := by
  change IsOpen ({x | ∀ i : Fin n, i.val < lo → a i < x} ∩
    {x | ∀ i : Fin n, hi ≤ i.val → x < a i})
  apply IsOpen.inter
  · simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_Ioi
  · simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_Iio

lemma slab_nonempty {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a) (k : ℕ) :
    (slab a k).Nonempty := by
  let A := (univ.filter fun i : Fin n => i.val < k).image a
  let B := (univ.filter fun i : Fin n => k ≤ i.val).image a
  obtain ⟨x,hA,hB⟩ := between_finsets A B (by
    intro v hv w hw
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hw
    apply ha
    change i.val<j.val
    exact lt_of_lt_of_le (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  refine ⟨x,fun i hi => hA _ ?_,fun i hi => hB _ ?_⟩
  · exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩
  · exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩

lemma slab_no_event {n : ℕ} {a : Fin n → ℝ} {k : ℕ} {x : ℝ}
    (hx : x ∈ slab a k) (i : Fin n) : x ≠ a i := by
  by_cases h : i.val < k
  · exact ne_of_gt (hx.1 i h)
  · exact ne_of_lt (hx.2 i (le_of_not_gt h))

lemma count_lt_iff {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a) (x : ℝ) (i : Fin n) :
    i.val < (univ.filter fun j => a j < x).card ↔ a i < x := by
  constructor
  · intro hi
    by_contra hn
    have hs : (univ.filter fun j => a j < x) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      apply ha.lt_iff_lt.mp
      exact (mem_filter.mp hj).2.trans_le (le_of_not_gt hn)
    have hh := Finset.card_le_card hs
    simp only [Fin.card_Iio] at hh
    omega
  · intro hi
    have hs : Finset.Iic i ⊆ (univ.filter fun j => a j < x) := by
      intro j hj
      exact mem_filter.mpr ⟨mem_univ j,(ha.monotone (Finset.mem_Iic.mp hj)).trans_lt hi⟩
    have hh := Finset.card_le_card hs
    simp only [Fin.card_Iic] at hh
    omega

lemma cover_slabs {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a) {x : ℝ}
    (hx : ∀ i, x ≠ a i) : ∃ k ≤ n, x ∈ slab a k := by
  let k := (univ.filter fun j => a j < x).card
  refine ⟨k,(card_filter_le _ _).trans (by simp),?_,?_⟩
  · intro i hi
    exact (count_lt_iff ha x i).mp hi
  · intro i hi
    have hn : ¬a i < x := fun h => (not_lt_of_ge hi) ((count_lt_iff ha x i).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt hn) (hx i)

lemma slab_unique {n : ℕ} {a : Fin n → ℝ} {x : ℝ} {k l : ℕ}
    (hk : k ≤ n) (hl : l ≤ n) (hxk : x ∈ slab a k) (hxl : x ∈ slab a l) : k=l := by
  rcases lt_trichotomy k l with h | h | h
  · have hn : k<n := lt_of_lt_of_le h hl
    have h1 := hxk.2 ⟨k,hn⟩ (by rfl)
    have h2 := hxl.1 ⟨k,hn⟩ h
    exact False.elim (lt_asymm h1 h2)
  · exact h
  · have hn : l<n := lt_of_lt_of_le h hk
    have h1 := hxl.2 ⟨l,hn⟩ (by rfl)
    have h2 := hxk.1 ⟨l,hn⟩ h
    exact False.elim (lt_asymm h1 h2)

lemma slab_subset_span {n : ℕ} {a : Fin n → ℝ} {lo hi k : ℕ}
    (hl : lo ≤ k) (hh : k ≤ hi) : slab a k ⊆ span a lo hi := by
  intro x hx
  exact ⟨fun i hi => hx.1 i (hi.trans_le hl),fun i hi => hx.2 i (hh.trans hi)⟩

lemma event_mem_span {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
    {lo hi : ℕ} {j : Fin n} (hlo : lo ≤ j.val) (hhi : j.val < hi) :
    a j ∈ span a lo hi :=
  ⟨fun _ hi => ha (hi.trans_le hlo),fun _ hi => ha (hhi.trans_le hi)⟩

lemma span_decomposition {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
    {lo hi : ℕ} (hlo : lo ≤ hi) (hhi : hi ≤ n) {x : ℝ} (hx : x ∈ span a lo hi) :
    (∃ j : Fin n, lo ≤ j.val ∧ j.val < hi ∧ x=a j) ∨
      ∃ k, lo ≤ k ∧ k ≤ hi ∧ x ∈ slab a k := by
  by_cases he : ∃ j, x=a j
  · obtain ⟨j,rfl⟩ := he
    left
    refine ⟨j,?_,?_,rfl⟩
    · by_contra hn
      exact lt_irrefl _ (hx.1 j (lt_of_not_ge hn))
    · by_contra hn
      exact lt_irrefl _ (hx.2 j (le_of_not_gt hn))
  · push Not at he
    obtain ⟨k,hk,hxk⟩ := cover_slabs ha he
    right
    refine ⟨k,?_,?_,hxk⟩
    · by_contra hn
      have hkl : k<lo := lt_of_not_ge hn
      by_cases hkn : k<n
      · exact lt_asymm (hxk.2 ⟨k,hkn⟩ le_rfl) (hx.1 ⟨k,hkn⟩ hkl)
      · omega
    · by_contra hn
      have hh : hi<k := lt_of_not_ge hn
      have hin : hi<n := hh.trans_le hk
      exact lt_asymm (hx.2 ⟨hi,hin⟩ le_rfl) (hxk.1 ⟨hi,hin⟩ hh)

end PlanarUnitDistances.SweepIntervals

namespace PlanarUnitDistances.Sweep
open Finset Classical

lemma sorted_heights {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : Set.InjOn f S) :
    ∃ L : List α, L.Nodup ∧ (∀ a, a ∈ L ↔ a ∈ S) ∧
      L.Pairwise (fun a b => f a < f b) := by
  classical
  let : LinearOrder S := LinearOrder.lift' (fun a => f a) (by
    intro a b h
    exact Subtype.ext (hf a.property b.property h))
  let L := (Finset.univ : Finset S).sort
  refine ⟨L.map Subtype.val,?_,?_,?_⟩
  · exact List.Nodup.map Subtype.val_injective (Finset.sort_nodup _ _)
  · intro a
    simp only [List.mem_map,L,Finset.mem_sort,Finset.mem_univ,true_and]
    exact ⟨fun ⟨b,hb⟩ => hb ▸ b.property,fun ha => ⟨⟨a,ha⟩,rfl⟩⟩
  · exact List.pairwise_map.mpr (Finset.sortedLT_sort _).pairwise

end PlanarUnitDistances.Sweep

namespace PlanarUnitDistances.CircleCutting
open Finset Classical

abbrev Label := Plane × Bool
noncomputable def labels (Q : Finset Plane) : Finset Label := Q ×ˢ Finset.univ
noncomputable def height (b : Label) : ℝ → ℝ := branch b.1 b.2
noncomputable def activeLabels (Q : Finset Plane) (x : ℝ) : Finset Label :=
  (labels Q).filter (fun b => active b.1 x)

lemma mem_labels {Q : Finset Plane} {b : Label} : b ∈ labels Q ↔ b.1 ∈ Q := by
  simp [labels]

lemma mem_activeLabels {Q : Finset Plane} {b : Label} {x : ℝ} :
    b ∈ activeLabels Q x ↔ b.1 ∈ Q ∧ active b.1 x := by
  simp [activeLabels,mem_labels]

lemma height_injOn {Q : Finset Plane} {x : ℝ} (hx : x ∉ eventAbscissas Q) :
    Set.InjOn (fun b => height b x) (activeLabels Q x) := by
  intro b hb d hd he
  by_contra hne
  exact hx (branch_collision_event (mem_activeLabels.mp hb).1
    (mem_activeLabels.mp hd).1 (mem_activeLabels.mp hb).2
    (mem_activeLabels.mp hd).2 hne he)

lemma exists_ordered_branches {Q : Finset Plane} {x : ℝ} (hx : x ∉ eventAbscissas Q) :
    ∃ L : List Label, L.Nodup ∧ (∀ b, b ∈ L ↔ b ∈ activeLabels Q x) ∧
      L.Pairwise (fun b d => height b x < height d x) :=
  Sweep.sorted_heights _ _ (height_injOn hx)

noncomputable def circleEvents (Q : Finset Plane) (c : Plane) : Finset ℝ :=
  {c 0-1,c 0+1} ∪ Q.biUnion (fun d => if h : c=d then ∅ else
    ((finite_circle_intersection c d h).toFinset.image (· 0)))

lemma circleEvents_subset {Q : Finset Plane} {c : Plane} (hc : c ∈ Q) :
    circleEvents Q c ⊆ eventAbscissas Q := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (extrema_mem_events hc).1
    · rw [Finset.mem_singleton] at hx
      rw [hx]; exact (extrema_mem_events hc).2
  · obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    by_cases hcd : c=d
    · simp [hcd] at hxd
    · simp only [dite_eq_right hcd,Finset.mem_image,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] at hxd
      obtain ⟨p,hp,rfl⟩ := hxd
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨p,mem_circleIntersections hc hd hcd hp.1 hp.2,rfl⟩)

lemma circleEvents_card (Q : Finset Plane) (c : Plane) :
    (circleEvents Q c).card ≤ 2+2*Q.card := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add Finset.card_le_two
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun d _ => show
    (if h : c=d then ∅ else (finite_circle_intersection c d h).toFinset.image (· 0)).card ≤ 2 from ?_)).trans
  · simp [mul_comm]
  · split
    · simp
    · apply Finset.card_image_le.trans
      apply circle_intersection_card
      · assumption
      · intro p hp
        simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hp

lemma extrema_mem_circleEvents (Q : Finset Plane) (c : Plane) :
    c 0-1 ∈ circleEvents Q c ∧ c 0+1 ∈ circleEvents Q c := by
  constructor <;> apply Finset.mem_union_left <;> simp

lemma collision_mem_circleEvents {Q : Finset Plane} {c d : Plane}
    (hd : d ∈ Q) (hcd : c ≠ d) {p : Plane} (hc : dist p c=1) (hp : dist p d=1) :
    p 0 ∈ circleEvents Q c := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨d,hd,?_⟩
  simp only [dite_eq_right hcd,Finset.mem_image,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]
  exact ⟨p,⟨hc,hp⟩,rfl⟩

noncomputable def critical (Q : Finset Plane) (x : ℝ) : Finset Label :=
  (labels Q).filter (fun b => x ∈ circleEvents Q b.1)

lemma critical_card_sum (Q : Finset Plane) (E : Finset ℝ) :
    ∑ x ∈ E, (critical Q x).card ≤ 4*Q.card+4*Q.card^2 := by
  classical
  have he : ∑ x ∈ E, (critical Q x).card =
      ∑ b ∈ labels Q, (E ∩ circleEvents Q b.1).card := by
    simp only [critical,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.filter_mem_eq_inter,Finset.sum_filter]
  rw [he]
  apply (Finset.sum_le_sum (fun b _ =>
    (Finset.card_le_card Finset.inter_subset_right).trans (circleEvents_card Q b.1))).trans
  simp only [Finset.sum_const,Finset.card_product,labels,Finset.card_univ,Fintype.card_bool,smul_eq_mul]
  nlinarith

lemma active_constant_without_events {Q : Finset Plane} {c : Plane} {S : Set ℝ}
    (hS : S.OrdConnected) (hE : ∀ z ∈ S, z ∉ circleEvents Q c)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : active c x ↔ active c y := by
  have hlo : c 0-1 ∉ S := fun h => hE _ h (extrema_mem_circleEvents Q c).1
  have hhi : c 0+1 ∉ S := fun h => hE _ h (extrema_mem_circleEvents Q c).2
  exact and_congr (same_side_of_not_mem hS hlo hx hy).1
    (same_side_of_not_mem hS hhi hx hy).2

lemma height_ne_without_events {Q : Finset Plane} {b d : Label} {x : ℝ}
    (hbd : b ≠ d) (hd : d.1 ∈ Q) (hb : active b.1 x) (hdx : active d.1 x)
    (hx : x ∉ circleEvents Q b.1) : height b x ≠ height d x := by
  intro he
  by_cases hcd : b.1=d.1
  · have hsign : b.2 ≠ d.2 := fun h => hbd (Prod.ext hcd h)
    have hlt := branch_order hb
    change branch b.1 b.2 x=branch d.1 d.2 x at he
    rw [← hcd] at he
    cases hb2 : b.2 <;> cases hd2 : d.2
    all_goals simp only [hb2,hd2,ne_eq,not_true_eq_false] at hsign
    · rw [hb2,hd2] at he; exact hlt.ne he
    · rw [hb2,hd2] at he; exact hlt.ne' he
  · have hp : graphPoint b.1 b.2 x=graphPoint d.1 d.2 x := by
      ext i
      fin_cases i
      · rfl
      · exact he
    have hdx' : dist (graphPoint b.1 b.2 x) d.1=1 := by
      rw [hp]; exact graphPoint_unit d.2 ⟨hdx.1.le,hdx.2.le⟩
    exact hx (collision_mem_circleEvents hd hcd (graphPoint_unit b.2 ⟨hb.1.le,hb.2.le⟩) hdx')

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleCutting
open Finset Classical

lemma skeleton_constant {Q : Finset Plane} {S : Set ℝ} (hS : S.OrdConnected)
    (C : Finset Label) (hC : ∀ b ∈ labels Q, b ∉ C → ∀ z ∈ S, z ∉ circleEvents Q b.1)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    {L R : List Label} (hLn : L.Nodup) (hRn : R.Nodup)
    (hLm : ∀ b, b ∈ L ↔ b ∈ activeLabels Q x)
    (hRm : ∀ b, b ∈ R ↔ b ∈ activeLabels Q y)
    (hLo : L.Pairwise (fun b d => height b x < height d x))
    (hRo : R.Pairwise (fun b d => height b y < height d y)) :
    L.filter (· ∉ C) = R.filter (· ∉ C) := by
  have hm : ∀ b, b ∈ L.filter (· ∉ C) ↔ b ∈ R.filter (· ∉ C) := by
    intro b
    simp only [List.mem_filter,decide_eq_true_eq,hLm,hRm,mem_activeLabels]
    constructor
    · rintro ⟨⟨hb,hbx⟩,hbc⟩
      exact ⟨⟨hb,(active_constant_without_events hS
        (hC b (mem_labels.mpr hb) hbc) hx hy).mp hbx⟩,hbc⟩
    · rintro ⟨⟨hb,hby⟩,hbc⟩
      exact ⟨⟨hb,(active_constant_without_events hS
        (hC b (mem_labels.mpr hb) hbc) hx hy).mpr hby⟩,hbc⟩
  have hp : (L.filter (· ∉ C)).Pairwise (fun b d => height b y < height d y) := by
    apply (hLo.filter _).imp_of_mem
    intro b d hb hd hbd
    have hb' := List.mem_filter.mp hb
    have hd' := List.mem_filter.mp hd
    have hbx := mem_activeLabels.mp ((hLm b).mp hb'.1)
    have hdx := mem_activeLabels.mp ((hLm d).mp hd'.1)
    have he := hC b (mem_labels.mpr hbx.1) (of_decide_eq_true hb'.2)
    have he' := hC d (mem_labels.mpr hdx.1) (of_decide_eq_true hd'.2)
    apply order_constant hS (continuous_branch _ _).continuousOn
      (continuous_branch _ _).continuousOn (fun z hz => ?_) hx hy hbd
    exact height_ne_without_events (fun heq => by rw [heq] at hbd; exact lt_irrefl _ hbd)
      hdx.1 ((active_constant_without_events hS he hx hz).mp hbx.2)
      ((active_constant_without_events hS he' hx hz).mp hdx.2) (he z hz)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ h h' => False.elim (lt_asymm h h'))
    hp (hRo.filter _) ((List.perm_ext_iff_of_nodup (hLn.filter _) (hRn.filter _)).mpr hm)

lemma event_span_no_other {n : ℕ} {a : Fin n → ℝ} {k i : Fin n} {x : ℝ}
    (hx : x ∈ SweepIntervals.span a k.val (k.val+1)) (he : x=a i) : i=k := by
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · exact (ne_of_gt (hx.1 i h)) he
  · exact (ne_of_lt (hx.2 i (by omega))) he

lemma event_span_noncritical {Q : Finset Plane} {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ x, x ∈ eventAbscissas Q ↔ ∃ i, a i=x) (k : Fin n)
    {b : Label} (hb : b ∈ labels Q) (hbc : b ∉ critical Q (a k))
    {z : ℝ} (hz : z ∈ SweepIntervals.span a k.val (k.val+1)) :
    z ∉ circleEvents Q b.1 := by
  intro he
  have hbq := mem_labels.mp hb
  obtain ⟨i,hi⟩ := (ha z).mp (circleEvents_subset hbq he)
  have hik := event_span_no_other hz hi.symm
  rw [hik] at hi
  apply hbc
  exact Finset.mem_filter.mpr ⟨hb,hi ▸ he⟩

theorem event_skeleton {Q : Finset Plane} {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ x, x ∈ eventAbscissas Q ↔ ∃ i, a i=x) (k : Fin n)
    {x y : ℝ} (hx : x ∈ SweepIntervals.slab a k.val)
    (hy : y ∈ SweepIntervals.slab a (k.val+1))
    {L R : List Label} (hLn : L.Nodup) (hRn : R.Nodup)
    (hLm : ∀ b, b ∈ L ↔ b ∈ activeLabels Q x)
    (hRm : ∀ b, b ∈ R ↔ b ∈ activeLabels Q y)
    (hLo : L.Pairwise (fun b d => height b x < height d x))
    (hRo : R.Pairwise (fun b d => height b y < height d y)) :
    L.filter (· ∉ critical Q (a k)) = R.filter (· ∉ critical Q (a k)) := by
  apply skeleton_constant (SweepIntervals.span_ordConnected _ _ _) _
    (fun b hb hbc z hz => event_span_noncritical ha k hb hbc hz)
    (SweepIntervals.slab_subset_span le_rfl (Nat.le_succ _) hx)
    (SweepIntervals.slab_subset_span (Nat.le_succ _) le_rfl hy)
    hLn hRn hLm hRm hLo hRo

end PlanarUnitDistances.CircleCutting

end OAI
