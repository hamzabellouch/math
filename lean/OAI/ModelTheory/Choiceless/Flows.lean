import OAI.ModelTheory.Choiceless.Counting

namespace OAI

noncomputable section

namespace CPTSeparation.Projection

open Finset

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

private def ind {α : Type*} [DecidableEq α] (S : Finset α) (a : α) : ℕ :=
  if a ∈ S then 1 else 0

private theorem ind_sq {α : Type*} [DecidableEq α] (S : Finset α) (a : α) :
    ind S a ^ 2 = ind S a := by simp [ind]

private theorem sum_ind {α : Type*} [DecidableEq α] [Fintype α] (S : Finset α) :
    ∑ a, ind S a = S.card := by simp [ind]

theorem card_sq_le_projections (R : Finset (X × Y × Z)) :
    R.card^2 ≤ (R.image (fun v => (v.1,v.2.1))).card *
      (R.image (fun v => (v.1,v.2.2))).card * (R.image (fun v => (v.2.1,v.2.2))).card := by
  let A := R.image (fun v => (v.1,v.2.1))
  let B := R.image (fun v => (v.1,v.2.2))
  let D := R.image (fun v => (v.2.1,v.2.2))
  let a (p : X × Y) := ind A p
  let b (p : X × Z) := ind B p
  let d (p : Y × Z) := ind D p
  let c (p : X × Y) := ∑ k, b (p.1,k) * d (p.2,k)
  have hr : R.card ≤ ∑ p, a p * c p := by
    rw [←sum_ind R]
    simp only [Fintype.sum_prod_type]
    dsimp [c]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    dsimp [a,b,d]
    by_cases h : (i,j,k) ∈ R
    · have ha : (i,j) ∈ A := mem_image.mpr ⟨(i,j,k),h,rfl⟩
      have hb : (i,k) ∈ B := mem_image.mpr ⟨(i,j,k),h,rfl⟩
      have hd : (j,k) ∈ D := mem_image.mpr ⟨(i,j,k),h,rfl⟩
      simp [ind,h,ha,hb,hd]
    · simp [ind,h]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := (univ : Finset (X × Y))) a c
  have ha : ∑ p : X × Y, a p^2 = A.card := by simp only [a,ind_sq,sum_ind]
  have hc : ∑ p : X × Y, c p^2 ≤ B.card * D.card := by
    calc
      _ ≤ ∑ p : X × Y, (∑ k, b (p.1,k)^2) * (∑ k, d (p.2,k)^2) := by
        apply Finset.sum_le_sum
        intro p _
        exact Finset.sum_mul_sq_le_sq_mul_sq univ (fun k => b (p.1,k)) (fun k => d (p.2,k))
      _ = B.card * D.card := by
        simp only [b,d,ind_sq,Fintype.sum_prod_type]
        rw [←Finset.sum_mul_sum]
        rw [←Fintype.sum_prod_type,←Fintype.sum_prod_type,sum_ind,sum_ind]
  calc
    R.card^2 ≤ (∑ p, a p*c p)^2 := Nat.pow_le_pow_left hr 2
    _ ≤ (∑ p, a p^2) * ∑ p, c p^2 := hcs
    _ ≤ A.card * (B.card*D.card) := by rw [ha]; exact Nat.mul_le_mul_left _ hc
    _ = _ := by dsimp [A,B,D]; simp only [mul_assoc]

end CPTSeparation.Projection

namespace CPTSeparation.BoxLines

open Finset

variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

def projection (R : Finset (Fin (n+1) × J)) : Finset J := R.image Prod.snd

def fullLines (R : Finset (Fin (n+1) × J)) : Finset J :=
  univ.filter fun j => ∀ i, (i,j) ∈ R

def edgeBoundary (R : Finset (Fin (n+1) × J)) : Finset (Fin n × J) :=
  univ.filter fun p => ¬ ((p.1.castSucc,p.2) ∈ R ↔ (p.1.succ,p.2) ∈ R)

private theorem fin_constant {P : Fin (n+1) → Prop}
    (h : ∀ i : Fin n, P i.castSucc ↔ P i.succ) (i : Fin (n+1)) : P i ↔ P 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact (h i).symm.trans ih

theorem partial_line_boundary (R : Finset (Fin (n+1) × J)) {j : J}
    (hj : j ∈ projection R \ fullLines R) :
    ∃ i : Fin n, (i,j) ∈ edgeBoundary R := by
  classical
  by_contra hn
  have h : ∀ i : Fin n, (i.castSucc,j) ∈ R ↔ (i.succ,j) ∈ R := by
    intro i
    by_contra hh
    exact hn ⟨i,by simp [edgeBoundary,hh]⟩
  obtain ⟨hj,hf⟩ := mem_sdiff.mp hj
  obtain ⟨⟨i,j'⟩,hi,he⟩ := mem_image.mp hj
  dsimp at he
  subst j'
  have hzero := (fin_constant (P := fun i => (i,j) ∈ R) h i).mp hi
  apply hf
  simp only [fullLines,mem_filter,mem_univ,true_and]
  intro i
  exact (fin_constant (P := fun i => (i,j) ∈ R) h i).mpr hzero

theorem line_count (R : Finset (Fin (n+1) × J)) :
    (n+1) * (projection R).card ≤ (n+1) * (edgeBoundary R).card + R.card := by
  classical
  have hF : fullLines R ⊆ projection R := by
    intro j hj
    have h := (mem_filter.mp hj).2
    exact mem_image.mpr ⟨(0,j),h 0,rfl⟩
  have hfull : (n+1) * (fullLines R).card ≤ R.card := by
    have hh : (univ : Finset (Fin (n+1))) ×ˢ fullLines R ⊆ R := by
      rintro ⟨i,j⟩ hp
      exact (mem_filter.mp (mem_product.mp hp).2).2 i
    simpa only [card_product,card_univ,Fintype.card_fin] using card_le_card hh
  have hpartial : (projection R \ fullLines R).card ≤ (edgeBoundary R).card := by
    have hh : projection R \ fullLines R ⊆ (edgeBoundary R).image Prod.snd := by
      intro j hj
      obtain ⟨i,hi⟩ := partial_line_boundary R hj
      exact mem_image.mpr ⟨(i,j),hi,rfl⟩
    exact (card_le_card hh).trans card_image_le
  have hc := card_sdiff_add_card_eq_card hF
  calc
    (n+1) * (projection R).card =
        (n+1) * (projection R \ fullLines R).card + (n+1) * (fullLines R).card := by
      rw [←hc,Nat.mul_add]
    _ ≤ (n+1) * (edgeBoundary R).card + R.card :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hpartial) hfull

end CPTSeparation.BoxLines

namespace CPTSeparation.Grid

section

open Finset

variable {n : ℕ}

def edgeBoundary (R : Finset (Vertex n)) : Finset (Edge n) :=
  univ.filter fun e => ¬(tail e ∈ R ↔ head e ∈ R)

def swapXY (v : Vertex n) : Vertex n := (v.2.1,v.1,v.2.2)

def moveZ (v : Vertex n) : Vertex n := (v.2.2,v.1,v.2.1)

theorem swapXY_injective : Function.Injective (@swapXY n) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
  simp only [swapXY,Prod.mk.injEq] at h ⊢
  tauto

theorem moveZ_injective : Function.Injective (@moveZ n) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
  simp only [moveZ,Prod.mk.injEq] at h ⊢
  tauto

private theorem boundary_x_le (R : Finset (Vertex n)) :
    (BoxLines.edgeBoundary R).card ≤ (edgeBoundary R).card := by
  apply card_le_card_of_injOn (fun p => ex p.1 p.2.1 p.2.2)
  · rintro ⟨i,j,k⟩ hp
    have hp' := (Finset.mem_filter.mp (show (i,j,k) ∈ BoxLines.edgeBoundary R from hp)).2
    apply Finset.mem_filter.mpr
    exact ⟨mem_univ _,hp'⟩
  · intro p _ q _ h
    exact Sum.inl.inj h

private theorem boundary_y_le (R : Finset (Vertex n)) :
    (BoxLines.edgeBoundary (R.image swapXY)).card ≤ (edgeBoundary R).card := by
  apply card_le_card_of_injOn (fun p => ey p.2.1 p.1 p.2.2)
  · rintro ⟨j,i,k⟩ hp
    have he (v : Vertex n) : swapXY v ∈ R.image swapXY ↔ v ∈ R :=
      by
        constructor
        · intro h
          obtain ⟨w,hw,he⟩ := mem_image.mp h
          simpa only [swapXY_injective he] using hw
        · intro h; exact mem_image.mpr ⟨v,h,rfl⟩
    have h1 := he (i,j.castSucc,k)
    have h2 := he (i,j.succ,k)
    have hp' := (Finset.mem_filter.mp (show (j,i,k) ∈ BoxLines.edgeBoundary (R.image swapXY) from hp)).2
    apply Finset.mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change ¬ ((i,j.castSucc,k) ∈ R ↔ (i,j.succ,k) ∈ R)
    change ¬(swapXY (i,j.castSucc,k) ∈ R.image swapXY ↔ swapXY (i,j.succ,k) ∈ R.image swapXY) at hp'
    simpa only [he] using hp'
  · rintro ⟨j,i,k⟩ _ ⟨j',i',k'⟩ _ h
    simp only [ey,Sum.inr.injEq,Sum.inl.injEq,Prod.mk.injEq] at h ⊢
    tauto

private theorem boundary_z_le (R : Finset (Vertex n)) :
    (BoxLines.edgeBoundary (R.image moveZ)).card ≤ (edgeBoundary R).card := by
  apply card_le_card_of_injOn (fun p => ez p.2.1 p.2.2 p.1)
  · rintro ⟨k,i,j⟩ hp
    have he (v : Vertex n) : moveZ v ∈ R.image moveZ ↔ v ∈ R :=
      by
        constructor
        · intro h
          obtain ⟨w,hw,he⟩ := mem_image.mp h
          simpa only [moveZ_injective he] using hw
        · intro h; exact mem_image.mpr ⟨v,h,rfl⟩
    have h1 := he (i,j,k.castSucc)
    have h2 := he (i,j,k.succ)
    have hp' := (Finset.mem_filter.mp (show (k,i,j) ∈ BoxLines.edgeBoundary (R.image moveZ) from hp)).2
    apply Finset.mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change ¬ ((i,j,k.castSucc) ∈ R ↔ (i,j,k.succ) ∈ R)
    change ¬(moveZ (i,j,k.castSucc) ∈ R.image moveZ ↔ moveZ (i,j,k.succ) ∈ R.image moveZ) at hp'
    simpa only [he] using hp'
  · rintro ⟨k,i,j⟩ _ ⟨k',i',j'⟩ _ h
    simp only [ez,Sum.inr.injEq,Prod.mk.injEq] at h ⊢
    tauto

theorem projection_line_bounds (R : Finset (Vertex n)) :
    let A := (R.image fun v => (v.1,v.2.1)).card
    let B := (R.image fun v => (v.1,v.2.2)).card
    let D := (R.image fun v => (v.2.1,v.2.2)).card
    (n+1)*A ≤ (n+1)*(edgeBoundary R).card + R.card ∧
    (n+1)*B ≤ (n+1)*(edgeBoundary R).card + R.card ∧
    (n+1)*D ≤ (n+1)*(edgeBoundary R).card + R.card := by
  have hx := (BoxLines.line_count R).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) (boundary_x_le R)) _)
  have hy := (BoxLines.line_count (R.image swapXY)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) (boundary_y_le R)) _)
  have hz := (BoxLines.line_count (R.image moveZ)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) (boundary_z_le R)) _)
  simp only [card_image_of_injective _ swapXY_injective,BoxLines.projection,
    image_image,Function.comp_def,swapXY] at hy
  simp only [card_image_of_injective _ moveZ_injective,BoxLines.projection,
    image_image,Function.comp_def,moveZ] at hz
  exact ⟨hz,hy,hx⟩

end

noncomputable def boxConstant : ℝ := 1 - (2:ℝ)^(-(1:ℝ)/3)

theorem boxConstant_pos : 0 < boxConstant := by
  unfold boxConstant
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
    (by norm_num : -(1:ℝ)/3 < 0)
  simpa using h

private theorem boundary_algebra {L r d p : ℝ} (hL : 0 < L) (hr : 0 < r)
    (_ : 0 ≤ d) (hp : 0 ≤ p) (hhalf : 2*r ≤ L^3)
    (hproj : r^2 ≤ p^3) (hline : L*p ≤ L*d+r) :
    boxConstant * r^((2:ℝ)/3) ≤ d := by
  have hr0 := le_of_lt hr
  have h23 : (r^((2:ℝ)/3))^3 = r^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr0]
    norm_num
  have h13 : (r^((1:ℝ)/3))^3 = r := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr0]
    norm_num
  have hc3 : ((2:ℝ)^(-(1:ℝ)/3))^3 = (1:ℝ)/2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hc : 0 ≤ (2:ℝ)^(-(1:ℝ)/3) := Real.rpow_nonneg (by norm_num) _
  have hp' : r^((2:ℝ)/3) ≤ p := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hr0 _) hp (by norm_num : (3:ℕ) ≠ 0)).mp
    simpa only [h23] using hproj
  have hl' : r^((1:ℝ)/3) ≤ (2:ℝ)^(-(1:ℝ)/3)*L := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hr0 _)
      (mul_nonneg hc hL.le) (by norm_num : (3:ℕ) ≠ 0)).mp
    rw [h13,mul_pow,hc3]
    linarith
  have hprod : r^((1:ℝ)/3)*r^((2:ℝ)/3) = r := by
    rw [←Real.rpow_add hr]
    norm_num
  have hsmall := mul_le_mul_of_nonneg_right hl' (Real.rpow_nonneg hr0 ((2:ℝ)/3))
  rw [hprod] at hsmall
  have hproj' := mul_le_mul_of_nonneg_left hp' hL.le
  unfold boxConstant
  nlinarith

theorem box_boundary {n : ℕ} (R : Finset (Vertex n)) (hne : R.Nonempty)
    (hhalf : 2*R.card ≤ (n+1)^3) :
    boxConstant * (R.card:ℝ)^((2:ℝ)/3) ≤ (edgeBoundary R).card := by
  let A := (R.image fun v => (v.1,v.2.1)).card
  let B := (R.image fun v => (v.1,v.2.2)).card
  let D := (R.image fun v => (v.2.1,v.2.2)).card
  let p := max A (max B D)
  have ha : A ≤ p := le_max_left _ _
  have hb : B ≤ p := (le_max_left B D).trans (le_max_right _ _)
  have hd : D ≤ p := (le_max_right B D).trans (le_max_right _ _)
  have hp : R.card^2 ≤ p^3 := by
    calc
      _ ≤ A*B*D := Projection.card_sq_le_projections R
      _ ≤ p*p*p := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hd
      _ = p^3 := by ring
  obtain ⟨hA,hB,hD⟩ := projection_line_bounds R
  have hline : (n+1)*p ≤ (n+1)*(edgeBoundary R).card + R.card := by
    dsimp [p]
    rw [mul_max_of_nonneg _ _ (Nat.zero_le _),mul_max_of_nonneg _ _ (Nat.zero_le _)]
    exact max_le hA (max_le hB hD)
  apply boundary_algebra (L := (n+1:ℕ)) (p := p)
  · positivity
  · exact_mod_cast Finset.card_pos.mpr hne
  · positivity
  · positivity
  · exact_mod_cast hhalf
  · exact_mod_cast hp
  · exact_mod_cast hline

end CPTSeparation.Grid

namespace CPTSeparation.Flows

section

open Classical

abbrev Scalar := ZMod 3

variable {V E : Type*} [finiteV : Fintype V] [finiteE : Fintype E] [decidableV : DecidableEq V] [decidableE : DecidableEq E]

def incidence (tail head : E → V) : (E → Scalar) →ₗ[Scalar] (V → Scalar) where
  toFun t := ∑ e, t e • (Pi.single (head e) 1 - Pi.single (tail e) 1)
  map_add' := by intros; simp [add_smul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [smul_smul,Finset.smul_sum]

omit V E in
@[simp] theorem incidence_single.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E] (tail head : E → V) (e : E) (z : Scalar) :
    incidence tail head (Pi.single e z) = Pi.single (head e) z - Pi.single (tail e) z := by
  change (∑ x, (Pi.single e z : E → Scalar) x •
    (Pi.single (head x) 1 - Pi.single (tail x) 1)) = _
  rw [Finset.sum_eq_single e]
  · simp [smul_sub,←Pi.single_smul]
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

def edgeRelation (tail head : E → V) (T : Finset E) (x y : V) : Prop :=
  ∃ e, e ∉ T ∧ tail e = x ∧ head e = y

def connected (tail head : E → V) (T : Finset E) : Setoid V :=
  Relation.EqvGen.setoid (edgeRelation tail head T)

abbrev Component (tail head : E → V) (T : Finset E) := Quotient (connected tail head T)

def component (tail head : E → V) (T : Finset E) (v : V) : Finset V :=
  Finset.univ.filter fun w => (connected tail head T).r v w

variable (tail head : E → V) (T : Finset E)

omit V E tail head T in
@[simp] theorem mem_component.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) (v w : V) : w ∈ component tail head T v ↔
    (connected tail head T).r v w := by simp [component]

omit V E tail head T in
theorem edge_connected.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) (e : E) (he : e ∉ T) :
    (connected tail head T).r (tail e) (head e) :=
  Relation.EqvGen.rel _ _ ⟨e,he,rfl,rfl⟩

omit V E tail head T in
theorem path_flow.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) {v w : V} (h : (connected tail head T).r v w) :
    ∃ t : E → Scalar, (∀ e ∈ T, t e = 0) ∧
      incidence tail head t = Pi.single w 1 - Pi.single v 1 := by
  induction h with
  | rel v w h =>
    obtain ⟨e,he,rfl,rfl⟩ := h
    refine ⟨Pi.single e 1,?_,incidence_single tail head e 1⟩
    intro f hf
    exact Pi.single_eq_of_ne (by intro h; subst f; exact he hf) _
  | refl v => exact ⟨0,by simp,by simp⟩
  | symm v w h ih =>
    obtain ⟨t,ht,hd⟩ := ih
    refine ⟨-t,by simpa using ht,?_⟩
    rw [map_neg,hd]; abel
  | trans u v w _ _ ih ih' =>
    obtain ⟨t,ht,hd⟩ := ih
    obtain ⟨t',ht',hd'⟩ := ih'
    refine ⟨t+t',fun e he => by simp [ht e he,ht' e he],?_⟩
    rw [map_add,hd,hd']; abel

omit V in
private theorem sum_single.{uDecl1}
    {V : Type uDecl1}
    [Fintype V]
    [DecidableEq V] (U : Finset V) (v : V) (z : Scalar) :
    ∑ x ∈ U, (Pi.single v z : V → Scalar) x = if v ∈ U then z else 0 := by
  simp [Pi.single_apply]

omit V E tail head in
theorem sum_incidence.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) (t : E → Scalar) : ∑ v, incidence tail head t v = 0 := by
  change (∑ v, (∑ e, t e • (Pi.single (head e) 1 - Pi.single (tail e) 1) : V → Scalar) v) = _
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,mul_sub]
  rw [Finset.sum_comm]
  have h (e : E) : ∑ v, (t e * (Pi.single (head e) (1:Scalar) : V → Scalar) v -
      t e * (Pi.single (tail e) (1:Scalar) : V → Scalar) v) = 0 := by
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum]
    simp [Pi.single_apply]
  simp only [h,Finset.sum_const_zero]

theorem sum_incidence_component (t : E → Scalar) (ht : ∀ e ∈ T, t e = 0) (v : V) :
    ∑ w ∈ component tail head T v, incidence tail head t w = 0 := by
  change (∑ w ∈ component tail head T v,
    (∑ e, t e • (Pi.single (head e) 1 - Pi.single (tail e) 1) : V → Scalar) w) = _
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,mul_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,sum_single,sum_single]
  by_cases he : e ∈ T
  · simp [ht e he]
  have hc : head e ∈ component tail head T v ↔ tail e ∈ component tail head T v := by
    simp only [mem_component]
    exact ⟨fun h => (connected tail head T).trans h ((connected tail head T).symm (edge_connected tail head T e he)),
      fun h => (connected tail head T).trans h (edge_connected tail head T e he)⟩
  simp only [hc,sub_self]

theorem solvable_iff (b : V → Scalar) :
    (∃ t : E → Scalar, (∀ e ∈ T, t e = 0) ∧ incidence tail head t = b) ↔
      ∀ v, ∑ w ∈ component tail head T v, b w = 0 := by
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact sum_incidence_component tail head T t ht
  · intro hb
    let q : V → Component tail head T := Quotient.mk (connected tail head T)
    let : Fintype (Component tail head T) := Fintype.ofFinite _
    have hp (v : V) : ∃ t : E → Scalar, (∀ e ∈ T, t e = 0) ∧
        incidence tail head t = Pi.single v 1 - Pi.single ((q v).out) 1 := by
      apply path_flow tail head T
      exact Quotient.exact (Quotient.out_eq (q v))
    choose t ht hd using hp
    refine ⟨∑ v, b v • t v,?_,?_⟩
    · intro e he
      simp [Finset.sum_apply,ht _ e he]
    · rw [map_sum]
      simp only [map_smul,hd,smul_sub,Finset.sum_sub_distrib]
      have hfirst : (∑ v, b v • (Pi.single v (1:Scalar) : V → Scalar)) = b := by
        funext j; simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
      have hsecond : (∑ v, b v • (Pi.single (q v).out (1:Scalar) : V → Scalar)) = 0 := by
        rw [←Fintype.sum_fiberwise q]
        apply Finset.sum_eq_zero
        intro c _
        have hf : (∑ v : {v : V // q v = c}, b v) = 0 := by
          have he (v : V) : q v = c ↔ v ∈ component tail head T c.out := by
            rw [mem_component]
            constructor
            · intro h
              exact Quotient.exact ((Quotient.out_eq c).trans h.symm)
            · intro h
              exact (Quotient.sound h).symm.trans (Quotient.out_eq c)
          let ee := Equiv.subtypeEquivRight he
          have hs := Fintype.sum_equiv ee (fun v : {v : V // q v = c} => b v)
            (fun v : component tail head T c.out => b v) (fun _ => rfl)
          rw [hs]
          exact (Finset.sum_coe_sort (component tail head T c.out) b).trans (hb c.out)
        have hx : (∑ v : {v : V // q v = c}, b v •
            (Pi.single (q v).out (1:Scalar) : V → Scalar)) =
            (∑ v : {v : V // q v = c}, b v) • Pi.single c.out 1 := by
          rw [Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro v _; rw [v.2]
        rw [hx,hf,zero_smul]
      rw [hfirst,hsecond,sub_zero]

theorem partial_flow_iff (σ : E → Scalar) :
    (∃ k : E → Scalar, incidence tail head k = 0 ∧ ∀ e ∈ T, k e = σ e) ↔
      ∀ v, ∑ w ∈ component tail head T v,
        incidence tail head (fun e => if e ∈ T then σ e else 0) w = 0 := by
  let z : E → Scalar := fun e => if e ∈ T then σ e else 0
  constructor
  · rintro ⟨k,hk,he⟩ v
    have ht : ∀ e ∈ T, (k-z) e = 0 := by intro e h; simp [z,h,he e h]
    have h := sum_incidence_component tail head T (k-z) ht v
    simpa [map_sub,hk,Finset.sum_neg_distrib] using h
  · intro h
    have hb : ∀ v, ∑ w ∈ component tail head T v, (-incidence tail head z) w = 0 := by
      intro v; simpa [Finset.sum_neg_distrib] using congrArg Neg.neg (h v)
    obtain ⟨t,ht,hd⟩ := (solvable_iff tail head T (-incidence tail head z)).mpr hb
    refine ⟨z+t,by simp [hd],?_⟩
    intro e he; simp [z,he,ht e he]

end

open Classical Finset

variable {V E : Type*} [Fintype V] [finiteE : Fintype E] [decidableV : DecidableEq V] [decidableE : DecidableEq E]

variable (tail head : E → V) (T : Finset E)

instance : Fintype (Component tail head T) := Fintype.ofFinite _

def cell (c : Component tail head T) : Finset V := component tail head T c.out

def quotientMap (v : V) : Component tail head T := Quotient.mk (connected tail head T) v

omit V E tail head T in
@[simp] theorem mem_cell.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) (c : Component tail head T) (v : V) :
    v ∈ cell tail head T c ↔ quotientMap tail head T v = c := by
  rw [cell,mem_component]
  constructor
  · intro h
    exact (Quotient.sound h).symm.trans (Quotient.out_eq c)
  · intro h
    exact Quotient.exact ((Quotient.out_eq c).trans h.symm)

omit V E tail head T in
theorem cell_nonempty.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) (c : Component tail head T) : (cell tail head T c).Nonempty :=
  ⟨c.out,(mem_cell tail head T c c.out).mpr (Quotient.out_eq c)⟩

omit V E tail head T in
theorem cells_disjoint.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) {c d : Component tail head T} (h : c ≠ d) :
    Disjoint (cell tail head T c) (cell tail head T d) := by
  apply disjoint_left.mpr
  intro v hc hd
  exact h ((mem_cell tail head T c v).mp hc |>.symm.trans ((mem_cell tail head T d v).mp hd))

omit V E tail head T in
theorem sum_cells.{uDecl1, uDecl2, uDecl3}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) {M : Type uDecl3} [AddCommMonoid M] (f : V → M) :
    ∑ c : Component tail head T, ∑ v ∈ cell tail head T c, f v = ∑ v, f v := by
  have he (c : Component tail head T) :
      (∑ v ∈ cell tail head T c, f v) = ∑ v, if quotientMap tail head T v = c then f v else 0 := by
    rw [←sum_filter]
    congr 1
    ext v; simp
  simp only [he]
  rw [sum_comm]
  simp

omit V E tail head T in
theorem sum_card_cells.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) : ∑ c : Component tail head T, (cell tail head T c).card = Fintype.card V := by
  simpa using sum_cells tail head T (fun _ => (1:ℕ))

def edgeBoundary (U : Finset V) : Finset E := univ.filter fun e => ¬(tail e ∈ U ↔ head e ∈ U)

theorem boundary_cell_subset (c : Component tail head T) :
    edgeBoundary tail head (cell tail head T c) ⊆ T := by
  intro e he
  by_contra hn
  have hc := edge_connected tail head T e hn
  have hq : quotientMap tail head T (tail e) = quotientMap tail head T (head e) := Quotient.sound hc
  have hh := (mem_filter.mp he).2
  exact hh (by simp only [mem_cell,hq])

theorem sum_boundary_cells :
    ∑ c : Component tail head T, (edgeBoundary tail head (cell tail head T c)).card ≤ 2*T.card := by
  have he (c : Component tail head T) :
      (edgeBoundary tail head (cell tail head T c)).card =
      ∑ e ∈ T, if e ∈ edgeBoundary tail head (cell tail head T c) then 1 else 0 := by
    rw [←card_filter]
    congr 1
    ext e
    simp only [mem_filter]
    exact ⟨fun h => ⟨boundary_cell_subset tail head T c h,h⟩,fun h => h.2⟩
  simp only [he]
  rw [sum_comm]
  calc
    _ ≤ ∑ _ ∈ T, 2 := by
      apply sum_le_sum
      intro e _
      calc
        _ ≤ ∑ c : Component tail head T,
            ((if quotientMap tail head T (tail e) = c then 1 else 0) +
             (if quotientMap tail head T (head e) = c then 1 else 0)) := by
          apply sum_le_sum
          intro c _
          simp only [edgeBoundary,mem_filter,mem_univ,true_and,mem_cell]
          by_cases h1 : quotientMap tail head T (tail e) = c <;>
            by_cases h2 : quotientMap tail head T (head e) = c <;> simp [h1,h2]
        _ = 2 := by rw [sum_add_distrib]; simp
    _ = 2*T.card := by simp [mul_comm]

omit V E tail head T in
theorem small_failing_component.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) (b : V → Scalar) (hb : ∑ v, b v = 0)
    (hfail : ∃ c : Component tail head T, (∑ v ∈ cell tail head T c, b v) ≠ 0) :
    ∃ c : Component tail head T, (∑ v ∈ cell tail head T c, b v) ≠ 0 ∧
      2*(cell tail head T c).card ≤ Fintype.card V := by
  obtain ⟨c,hc⟩ := hfail
  by_cases hsmall : 2*(cell tail head T c).card ≤ Fintype.card V
  · exact ⟨c,hc,hsmall⟩
  have he : ∃ d : Component tail head T, d ≠ c ∧ (∑ v ∈ cell tail head T d, b v) ≠ 0 := by
    by_contra hh
    push Not at hh
    have hsum : (∑ d : Component tail head T, ∑ v ∈ cell tail head T d, b v) =
        ∑ v ∈ cell tail head T c, b v := by
      apply sum_eq_single c
      · intro d _ hd; exact hh d hd
      · simp
    rw [sum_cells,hb] at hsum
    exact hc hsum.symm
  obtain ⟨d,hd,hfd⟩ := he
  refine ⟨d,hfd,?_⟩
  have hdis := cells_disjoint tail head T hd.symm
  have hcard := card_le_card (subset_univ (cell tail head T c ∪ cell tail head T d))
  rw [card_union_of_disjoint hdis,card_univ] at hcard
  omega

end CPTSeparation.Flows

namespace CPTSeparation.Grid

open Classical Finset

variable {n : ℕ}

private theorem bound_of_boundary {r b : ℝ} (hr : 0 ≤ r) (_ : 0 ≤ b)
    (h : boxConstant * r^((2:ℝ)/3) ≤ b) : r ≤ (b/boxConstant)^((3:ℝ)/2) := by
  have hu : r^((2:ℝ)/3) ≤ b/boxConstant := by
    apply (le_div_iff₀ boxConstant_pos).mpr
    simpa only [mul_comm] using h
  have hv := Real.rpow_le_rpow (Real.rpow_nonneg hr _) hu (by norm_num : (0:ℝ) ≤ 3/2)
  rw [←Real.rpow_mul hr] at hv
  norm_num at hv
  exact hv

theorem small_cell_bound (T : Finset (Edge n)) (c : Flows.Component tail head T)
    (hsmall : 2*(Flows.cell tail head T c).card ≤ (n+1)^3) :
    ((Flows.cell tail head T c).card:ℝ) ≤
      ((Flows.edgeBoundary tail head (Flows.cell tail head T c)).card / boxConstant)^((3:ℝ)/2) :=
  bound_of_boundary (by positivity) (by positivity)
    (box_boundary _ (Flows.cell_nonempty tail head T c) hsmall)

theorem partial_flow_small_obstruction (T : Finset (Edge n)) (σ : Edge n → Scalar)
    (hfail : ¬ ∃ k : Edge n → Scalar, Flows.incidence tail head k = 0 ∧
      ∀ e ∈ T, k e = σ e) :
    ∃ c : Flows.Component tail head T,
      (∑ v ∈ Flows.cell tail head T c,
        Flows.incidence tail head (fun e => if e ∈ T then σ e else 0) v) ≠ 0 ∧
      2*(Flows.cell tail head T c).card ≤ (n+1)^3 ∧
      ((Flows.cell tail head T c).card:ℝ) ≤
        (T.card/boxConstant)^((3:ℝ)/2) := by
  let z : Edge n → Scalar := fun e => if e ∈ T then σ e else 0
  have hf : ∃ v, (∑ w ∈ Flows.component tail head T v, Flows.incidence tail head z w) ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hfail ((Flows.partial_flow_iff tail head T σ).mpr hh)
  obtain ⟨v,hv⟩ := hf
  have hcell : Flows.cell tail head T (Flows.quotientMap tail head T v) =
      Flows.component tail head T v := by
    ext w
    rw [Flows.mem_cell,Flows.mem_component]
    exact ⟨fun h => Quotient.exact h.symm,fun h => (Quotient.sound h).symm⟩
  obtain ⟨c,hc,hs⟩ := Flows.small_failing_component tail head T (Flows.incidence tail head z)
    (Flows.sum_incidence tail head z) ⟨Flows.quotientMap tail head T v,by simpa only [hcell] using hv⟩
  have hcard : Fintype.card (Vertex n) = (n+1)^3 := by simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
  rw [hcard] at hs
  refine ⟨c,hc,hs,(small_cell_bound T c hs).trans ?_⟩
  apply Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) boxConstant_pos.le) _ (by norm_num)
  apply div_le_div_of_nonneg_right _ boxConstant_pos.le
  exact_mod_cast card_le_card (Flows.boundary_cell_subset tail head T c)

private theorem sum_rpow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, (f i)^((3:ℝ)/2) ≤ (∑ i ∈ s, f i)^((3:ℝ)/2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha,sum_insert ha]
    have hs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    calc
      f a ^ ((3:ℝ)/2) + ∑ i ∈ s, f i ^ ((3:ℝ)/2) ≤
          f a ^ ((3:ℝ)/2) + (∑ i ∈ s, f i) ^ ((3:ℝ)/2) := add_le_add (le_refl _) (ih hs)
      _ ≤ (f a + ∑ i ∈ s, f i) ^ ((3:ℝ)/2) :=
        Real.add_rpow_le_rpow_add (hf a (mem_insert_self _ _)) (sum_nonneg hs) (by norm_num)

theorem small_components_bound (T : Finset (Edge n)) (S : Finset (Flows.Component tail head T))
    (hs : ∀ c ∈ S, 2*(Flows.cell tail head T c).card ≤ (n+1)^3) :
    (∑ c ∈ S, ((Flows.cell tail head T c).card:ℝ)) ≤
      ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) := by
  let b (c : Flows.Component tail head T) : ℝ :=
    (Flows.edgeBoundary tail head (Flows.cell tail head T c)).card / boxConstant
  have hn (c) : 0 ≤ b c := div_nonneg (Nat.cast_nonneg _) boxConstant_pos.le
  calc
    _ ≤ ∑ c ∈ S, (b c)^((3:ℝ)/2) := sum_le_sum (fun c hc => small_cell_bound T c (hs c hc))
    _ ≤ (∑ c ∈ S, b c)^((3:ℝ)/2) := sum_rpow_le S b (fun c _ => hn c)
    _ ≤ ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) := by
      apply Real.rpow_le_rpow (sum_nonneg (fun c _ => hn c)) _ (by norm_num)
      dsimp [b]
      rw [←sum_div]
      apply div_le_div_of_nonneg_right _ boxConstant_pos.le
      calc
        _ ≤ ∑ c : Flows.Component tail head T,
            ((Flows.edgeBoundary tail head (Flows.cell tail head T c)).card:ℝ) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
        _ ≤ 2*T.card := by exact_mod_cast Flows.sum_boundary_cells tail head T

theorem exists_giant (T : Finset (Edge n))
    (hnum : ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ)) :
    ∃ c : Flows.Component tail head T, (n+1)^3 < 2*(Flows.cell tail head T c).card := by
  by_contra hh
  push Not at hh
  have h := small_components_bound T univ (fun c _ => hh c)
  rw [←Nat.cast_sum,Flows.sum_card_cells] at h
  have hc : Fintype.card (Vertex n) = (n+1)^3 := by simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
  rw [hc] at h
  exact (not_lt_of_ge h) hnum

end CPTSeparation.Grid

namespace CPTSeparation.Flows

open Classical Finset

variable {V E : Type*} [finiteV : Fintype V] [finiteE : Fintype E] [decidableV : DecidableEq V] [decidableE : DecidableEq E]

variable (tail head : E → V)

omit V E tail head in
theorem connected_mono.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T U : Finset E} (hT : T ⊆ U) {v w : V}
    (h : (connected tail head U).r v w) : (connected tail head T).r v w := by
  induction h with
  | rel v w h =>
    obtain ⟨e,he,rfl,rfl⟩ := h
    exact edge_connected tail head T e (fun hh => he (hT hh))
  | refl v => exact .refl v
  | symm v w h ih => exact .symm _ _ ih
  | trans v w z h h' ih ih' => exact .trans _ _ _ ih ih'

omit V E tail head in
theorem component_mono.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T U : Finset E} (hT : T ⊆ U) (v : V) :
    component tail head U v ⊆ component tail head T v := by
  intro w hw
  exact (mem_component _ _ _ _ _).mpr (connected_mono tail head hT ((mem_component _ _ _ _ _).mp hw))

omit V E tail head in
theorem component_eq.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T : Finset E} {v w : V} (h : (connected tail head T).r v w) :
    component tail head T v = component tail head T w := by
  ext x; simp only [mem_component]
  exact ⟨fun hv => (connected tail head T).trans ((connected tail head T).symm h) hv,
    fun hw => (connected tail head T).trans h hw⟩

def IsGiant (T : Finset E) (v : V) : Prop :=
  Fintype.card V < 2*(component tail head T v).card

omit V E tail head in
theorem giant_mono.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T U : Finset E} (hT : T ⊆ U) {v : V} (h : IsGiant tail head U v) :
    IsGiant tail head T v := lt_of_lt_of_le h (Nat.mul_le_mul_left 2 (card_le_card (component_mono tail head hT v)))

omit V E tail head in
theorem giants_connected.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T : Finset E} {v w : V}
    (hv : IsGiant tail head T v) (hw : IsGiant tail head T w) : (connected tail head T).r v w := by
  by_contra hh
  have hd : Disjoint (component tail head T v) (component tail head T w) := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact hh ((connected tail head T).trans ((mem_component _ _ _ _ _).mp hx)
      ((connected tail head T).symm ((mem_component _ _ _ _ _).mp hx')))
  have hk : (component tail head T v).card + (component tail head T w).card ≤ Fintype.card V := by
    rw [←card_union_of_disjoint hd]
    exact card_le_univ _
  dsimp [IsGiant] at hv hw
  omega

omit V E tail head in
theorem component_isolated.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T : Finset E} (v : V)
    (h : ∀ e, tail e = v ∨ head e = v → e ∈ T) : component tail head T v = {v} := by
  have hh {x y : V} (hc : (connected tail head T).r x y) : x = v ↔ y = v := by
    induction hc with
    | rel x y hr =>
      obtain ⟨e,he,rfl,rfl⟩ := hr
      exact ⟨fun hv => False.elim (he (h e (Or.inl hv))),fun hv => False.elim (he (h e (Or.inr hv)))⟩
    | refl x => rfl
    | symm x y hc ih => exact ih.symm
    | trans x y z hc hc' ih ih' => exact ih.trans ih'
  ext w
  simp only [mem_component,mem_singleton]
  exact ⟨fun hw => (hh hw).mp rfl,fun hw => by subst w; exact (connected tail head T).refl _⟩

omit V E tail head in
theorem giant_ne_isolated.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T : Finset E} {w v : V} (hV : 2 ≤ Fintype.card V)
    (hw : IsGiant tail head T w) (h : ∀ e, tail e = v ∨ head e = v → e ∈ T) : w ≠ v := by
  intro he; subst w
  have hh := component_isolated tail head v h
  dsimp [IsGiant] at hw
  rw [hh,card_singleton] at hw
  omega

end CPTSeparation.Flows

namespace CPTSeparation.Grid

section

open Classical Finset

variable {n : ℕ}

theorem grid_connected (v w : Vertex n) : (Flows.connected tail head ∅).r v w := by
  have hx (i j k : Fin (n+1)) : (Flows.connected tail head ∅).r (0,j,k) (i,j,k) := by
    induction i using Fin.induction with
    | zero => exact (Flows.connected tail head ∅).refl _
    | succ i ih =>
      exact (Flows.connected tail head ∅).trans ih (Flows.edge_connected tail head ∅ (ex i j k) (by simp))
  have hy (i j k : Fin (n+1)) : (Flows.connected tail head ∅).r (i,0,k) (i,j,k) := by
    induction j using Fin.induction with
    | zero => exact (Flows.connected tail head ∅).refl _
    | succ j ih =>
      exact (Flows.connected tail head ∅).trans ih (Flows.edge_connected tail head ∅ (ey i j k) (by simp))
  have hz (i j k : Fin (n+1)) : (Flows.connected tail head ∅).r (i,j,0) (i,j,k) := by
    induction k using Fin.induction with
    | zero => exact (Flows.connected tail head ∅).refl _
    | succ k ih =>
      exact (Flows.connected tail head ∅).trans ih (Flows.edge_connected tail head ∅ (ez i j k) (by simp))
  have h (v : Vertex n) : (Flows.connected tail head ∅).r (0,0,0) v :=
    (Flows.connected tail head ∅).trans (hx v.1 0 0)
      ((Flows.connected tail head ∅).trans (hy v.1 v.2.1 0) (hz v.1 v.2.1 v.2.2))
  exact (Flows.connected tail head ∅).trans ((Flows.connected tail head ∅).symm (h v)) (h w)

theorem grid_empty_component (v : Vertex n) : Flows.component tail head ∅ v = univ := by
  ext w; simp only [Flows.mem_component,mem_univ,iff_true]; exact grid_connected v w

theorem grid_empty_giant (v : Vertex n) : Flows.IsGiant tail head ∅ v := by
  dsimp [Flows.IsGiant]
  rw [grid_empty_component,card_univ]
  have hpos : 0 < Fintype.card (Vertex n) := Fintype.card_pos_iff.mpr ⟨(0,0,0)⟩
  omega

end

section

open Classical Finset

variable {n M : ℕ} {b : Vertex n → Scalar}

theorem AtomShift.config_boundary {t : Edge n → Scalar} {v : Vertex n}
    {s : Configuration b v} {y : Atom b} (h : AtomShift t (.inr ⟨v,s⟩) y) :
    boundary t v = 0 := by
  cases h with
  | config v s h => simpa only [sub_self] using h

theorem quantitative_homogeneity_shift (hn : 1 ≤ n) {J : Type*} [Fintype J] [Nonempty (Atom b)]
    (names : J ↪ Fin M) (a a' : J → Atom b)
    (hw : (7*Fintype.card J:ℝ) + 7*((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a') :
    ∃ k : Edge n → Scalar, boundary k = 0 ∧ ∀ j, AtomShift k (a j) (a' j) := by
  let : Nonempty (Atom b) := ⟨.inr ⟨(0,0,0),someConfiguration hn b (0,0,0)⟩⟩
  have hp : 0 ≤ ((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2) := Real.rpow_nonneg (div_nonneg (by positivity) boxConstant_pos.le) _
  have hw' : 7*Fintype.card J < M := by
    have hh : (7*Fintype.card J:ℝ)+1 ≤ M := by linarith
    have hh' : 7*Fintype.card J+1 ≤ M := by exact_mod_cast hh
    omega
  obtain ⟨σ,hσ⟩ := tuple_partial_shift names a a' hw' ht
  let T : Finset (Edge n) := touches univ a
  have hT : T.card ≤ 6*Fintype.card J := by simpa [T] using touches_card univ a
  suffices hs : ∃ k : Edge n → Scalar, Flows.incidence tail head k = 0 ∧ ∀ e ∈ T, k e = σ e by
    obtain ⟨k,hk,he⟩ := hs
    refine ⟨k,hk,fun j => (hσ j).congr ?_⟩
    intro e hej
    exact (he e (touch_subset_touches univ a (mem_univ j) hej)).symm
  by_contra hs
  obtain ⟨C,hbad,hsmall,hcard⟩ := partial_flow_small_obstruction T σ hs
  let U := Flows.cell tail head T C
  have hU : (U.card:ℝ) ≤ ((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2) := by
    apply hcard.trans
    apply Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) boxConstant_pos.le) _ (by norm_num)
    apply div_le_div_of_nonneg_right _ boxConstant_pos.le
    exact_mod_cast hT
  let conf (v : U) : Atom b := .inr ⟨v.val,someConfiguration hn b v.val⟩
  have hwU : 7*Fintype.card (J ⊕ U) < M := by
    have hh : (7*(Fintype.card J+U.card):ℝ)+1 ≤ M := by linarith
    have hh' : 7*(Fintype.card J+U.card)+1 ≤ M := by exact_mod_cast hh
    simpa only [Fintype.card_sum,Fintype.card_coe] using (show 7*(Fintype.card J+U.card)<M by omega)
  have hcardU : Fintype.card (J ⊕ U) < M := by omega
  obtain ⟨conf',htU⟩ := Counting.tupleType_append (analysisStructure b) (analysisStructure b)
    names (namesBelow hcardU) a a' conf ht
  obtain ⟨d,hd⟩ := tuple_partial_shift (namesBelow hcardU) (Sum.elim a conf) (Sum.elim a' conf') hwU htU
  have hdT : ∀ e ∈ T, d e = σ e := by
    intro e he
    obtain ⟨j,hj,he⟩ := mem_biUnion.mp he
    exact (hd (.inl j)).unique_on_touch (hσ j) e he
  have hdU : ∀ v ∈ U, Flows.incidence tail head d v = 0 := by
    intro v hv
    exact (hd (.inr ⟨v,hv⟩)).config_boundary
  let z : Edge n → Scalar := fun e => if e ∈ T then σ e else 0
  have hd0 : ∀ e ∈ T, (d-z) e = 0 := by intro e he; simp [z,he,hdT e he]
  have hbal := Flows.sum_incidence_component tail head T (d-z) hd0 C.out
  have hsum : (∑ v ∈ U, Flows.incidence tail head d v) = 0 := sum_eq_zero hdU
  change (∑ v ∈ U, Flows.incidence tail head (d-z) v) = 0 at hbal
  simp only [map_sub,Pi.sub_apply,sum_sub_distrib,hsum,zero_sub,neg_eq_zero] at hbal
  exact hbad hbal

end

open Classical

variable {n M : ℕ} {b : Vertex n → Scalar}

theorem central_atomShift (k : CentralGroup n) (x : Atom b) :
    AtomShift k.toAdd.val x (k • x) := by
  have hk (e : Edge n) : restrictGroup e (Support.H.central flowCycle k.toAdd) =
      Support.H.central (localCycle e) (k.toAdd.val e) := by
    apply Support.H.ext <;> rfl
  cases x with
  | inl x =>
    rcases x with ⟨e,s⟩
    change AtomShift k.toAdd.val (.inl ⟨e,s⟩)
      (.inl ⟨e,restrictGroup e (Support.H.central flowCycle k.toAdd)*s⟩)
    rw [hk]
    exact .edge e s
  | inr x =>
    rcases x with ⟨v,s⟩
    have hb : boundary k.toAdd.val v = b v-b v := by
      have hh := congrFun k.toAdd.property v
      simp
    have hs : Support.H.central flowCycle k.toAdd • s = s.shift k.toAdd.val hb := by
      apply Configuration.ext
      intro e
      change restrictGroup e.val (Support.H.central flowCycle k.toAdd)*s.state e = _
      rw [hk]
      rfl
    change AtomShift k.toAdd.val (.inr ⟨v,s⟩) (.inr ⟨v,Support.H.central flowCycle k.toAdd • s⟩)
    rw [hs]
    exact .config v s hb

theorem quantitative_homogeneity (hn : 1 ≤ n) {J : Type*} [Fintype J] [Nonempty (Atom b)]
    (names : J ↪ Fin M) (a a' : J → Atom b)
    (hw : (7*Fintype.card J:ℝ) + 7*((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a') :
    ∃ k : CentralGroup n, ∀ j, k • a j = a' j := by
  obtain ⟨k,hk,ha⟩ := quantitative_homogeneity_shift hn names a a' hw ht
  let g : CentralGroup n := Multiplicative.ofAdd ⟨k,hk⟩
  exact ⟨g,fun j => (central_atomShift g (a j)).functional (ha j)⟩

theorem empty_homogeneity {J : Type*} [IsEmpty J] (a a' : J → Atom b) :
    ∃ k : CentralGroup n, ∀ j, k • a j = a' j := ⟨1,fun j => isEmptyElim j⟩

end CPTSeparation.Grid

namespace CPTSeparation.Counting.Formula

open Classical Finset

variable {R I A B : Type*} [DecidableEq I]

theorem eval_of_partialBijectionSystem (S : Structure R A) (T : Structure R B)
    (E : Finset I → (I → A) → (I → B) → Prop)
    (heq : ∀ names v w, E names v w → ∀ i ∈ names, ∀ j ∈ names, (v i = v j ↔ w i = w j))
    (hrel : ∀ names v w, E names v w → ∀ r i, i ∈ names → ∀ j, j ∈ names →
      (S.rel r (v i) (v j) ↔ T.rel r (w i) (w j)))
    (hext : ∀ names v w, E names v w → ∀ i, ∃ e : A ≃ B,
      ∀ a, E (insert i (names.erase i)) (Function.update v i a) (Function.update w i (e a)))
    (φ : Formula R I) : ∀ names v w, E names v w → φ.free ⊆ names →
      (φ.eval S v ↔ φ.eval T w) := by
  induction φ with
  | falsum => intros; rfl
  | equal i j =>
    intro names v w h hf
    exact heq names v w h i (hf (by simp [free])) j (hf (by simp [free]))
  | relation r i j =>
    intro names v w h hf
    exact hrel names v w h r i (hf (by simp [free])) j (hf (by simp [free]))
  | neg φ ih => intro names v w h hf; exact not_congr (ih names v w h hf)
  | and φ ψ ih ih' =>
    intro names v w h hf
    exact and_congr (ih names v w h (subset_union_left.trans hf))
      (ih' names v w h (subset_union_right.trans hf))
  | ex i φ ih =>
    intro names v w h hf
    obtain ⟨e,he⟩ := hext names v w h i
    have hfree : φ.free ⊆ insert i (names.erase i) := by
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hji,hf (mem_erase.mpr ⟨hji,hj⟩)⟩)
    change (∃ a, φ.eval S (Function.update v i a)) ↔ _
    constructor
    · rintro ⟨a,ha⟩; exact ⟨e a,(ih _ _ _ (he a) hfree).mp ha⟩
    · rintro ⟨b,hb⟩; obtain ⟨a,rfl⟩ := e.surjective b
      exact ⟨a,(ih _ _ _ (he a) hfree).mpr hb⟩
  | exact i n φ ih =>
    intro names v w h hf
    obtain ⟨e,he⟩ := hext names v w h i
    have hfree : φ.free ⊆ insert i (names.erase i) := by
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hji,hf (mem_erase.mpr ⟨hji,hj⟩)⟩)
    let f : {a : A // φ.eval S (Function.update v i a)} ≃
        {b : B // φ.eval T (Function.update w i b)} :=
      e.subtypeEquiv (fun a => ih _ _ _ (he a) hfree)
    exact ⟨fun ⟨g⟩ => ⟨f.symm.trans g⟩,fun ⟨g⟩ => ⟨f.trans g⟩⟩

end CPTSeparation.Counting.Formula

namespace CPTSeparation.Grid

open Classical Finset

variable {n M : ℕ} {b b' : Vertex n → Scalar}

theorem boundary_eq_incidence : (boundary : (Edge n → Scalar) →ₗ[Scalar] (Vertex n → Scalar)) =
    Flows.incidence tail head := rfl

def GiantBound (n M : ℕ) : Prop :=
  ((12*(M:ℝ))/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ)

theorem giant_exists_of_bound (hbound : GiantBound n M) (T : Finset (Edge n)) (hT : T.card ≤ 6*M) :
    ∃ v, Flows.IsGiant tail head T v := by
  have hnum : ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ) := by
    apply lt_of_le_of_lt _ hbound
    apply Real.rpow_le_rpow (div_nonneg (by positivity) boxConstant_pos.le) _ (by norm_num)
    apply div_le_div_of_nonneg_right _ boxConstant_pos.le
    have hh : (T.card:ℝ) ≤ 6*M := by exact_mod_cast hT
    linarith
  obtain ⟨c,hc⟩ := exists_giant T hnum
  refine ⟨c.out,?_⟩
  change Fintype.card (Vertex n) < 2*(Flows.cell tail head T c).card
  have hcard : Fintype.card (Vertex n) = (n+1)^3 := by
    simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
  simpa only [hcard] using hc

theorem defect_transport (hbound : GiantBound n M) (T U : Finset (Edge n)) (hTU : T ⊆ U)
    (hU : U.card ≤ 6*M) (t : Edge n → Scalar) (w : Vertex n)
    (hw : Flows.IsGiant tail head T w) (ht : boundary t = b'-b-Pi.single w 1) :
    ∃ t' : Edge n → Scalar, ∃ w' : Vertex n,
      Flows.IsGiant tail head U w' ∧ boundary t' = b'-b-Pi.single w' 1 ∧ ∀ e ∈ T, t' e = t e := by
  obtain ⟨w',hw'⟩ := giant_exists_of_bound hbound U hU
  have hc := Flows.giants_connected tail head (Flows.giant_mono tail head hTU hw') hw
  obtain ⟨p,hp,hd⟩ := Flows.path_flow tail head T hc
  refine ⟨t+p,w',hw',?_,?_⟩
  · rw [map_add,ht,boundary_eq_incidence,hd]
    abel
  · intro e he; simp [hp e he]

def CompatibleAssignment {I : Type*} [DecidableEq I] (names : Finset I)
    (a : I → Atom b) (a' : I → Atom b') : Prop :=
  ∃ t : Edge n → Scalar, ∃ w : Vertex n,
    Flows.IsGiant tail head (touches names a) w ∧ boundary t = b'-b-Pi.single w 1 ∧
    ∀ i ∈ names, AtomShift t (a i) (a' i)

theorem CompatibleAssignment.mono {I : Type*} [DecidableEq I] {names small : Finset I}
    (hs : small ⊆ names) {a : I → Atom b} {a' : I → Atom b'}
    (h : CompatibleAssignment names a a') : CompatibleAssignment small a a' := by
  obtain ⟨t,w,hw,ht,ha⟩ := h
  exact ⟨t,w,Flows.giant_mono tail head (touches_mono hs a) hw,ht,fun i hi => ha i (hs hi)⟩

theorem CompatibleAssignment.extend (hn : 1 ≤ n) (hbound : GiantBound n M)
    (names : Finset (Fin M)) (a : Fin M → Atom b) (a' : Fin M → Atom b')
    (h : CompatibleAssignment names a a') (i : Fin M) :
    ∃ e : Atom b ≃ Atom b', ∀ x,
      CompatibleAssignment (insert i (names.erase i)) (Function.update a i x) (Function.update a' i (e x)) := by
  obtain ⟨t,w,hw,ht,ha⟩ := h.mono (erase_subset i names)
  let T := touches (names.erase i) a
  have hcard : (names.erase i).card + 1 ≤ M := by
    have hsub : names.erase i ⊆ (univ : Finset (Fin M)).erase i := erase_subset_erase i (subset_univ _)
    have hh := card_le_card hsub
    have hpos := i.isLt
    rw [card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin] at hh
    omega
  have hj (J : Block n) : (T ∪ blockEdges J).card ≤ 6*M := by
    calc
      _ ≤ T.card + (blockEdges J).card := card_union_le _ _
      _ ≤ 6*(names.erase i).card + 6 := Nat.add_le_add (touches_card _ _) (blockEdges_card _)
      _ ≤ 6*M := by omega
  have hmove (J : Block n) := defect_transport hbound T (T ∪ blockEdges J)
    subset_union_left (hj J) t w hw ht
  choose tj wj hjg hjd hjs using hmove
  have hV : 2 ≤ Fintype.card (Vertex n) := by
    have hc : Fintype.card (Vertex n) = (n+1)^3 := by
      simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
    rw [hc]
    have hh : 2^3 ≤ (n+1)^3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hv (v : Vertex n) : boundary (tj (.inr v)) v = b' v-b v := by
    have hwv : wj (.inr v) ≠ v := Flows.giant_ne_isolated tail head hV (hjg (.inr v)) (by
      intro e he
      exact mem_union_right _ (by simpa [blockEdges,incident,or_comm] using he))
    have hh := congrFun (hjd (.inr v)) v
    simpa [Pi.single_apply,Ne.symm hwv] using hh
  let e := blockShiftEquiv (fun e => tj (.inl e)) (fun v => tj (.inr v)) hv
  refine ⟨e,fun x => ?_⟩
  let J := atomBlock x
  refine ⟨tj J,wj J,?_,hjd J,?_⟩
  · rw [touches_insert_update]
    exact hjg J
  · intro j hj'
    rcases mem_insert.mp hj' with rfl | hj'
    · simp only [Function.update_self]
      cases x with
      | inl x => rcases x with ⟨f,s⟩; exact AtomShift.edge f s
      | inr x => rcases x with ⟨v,s⟩; exact AtomShift.config v s (hv v)
    · have hji := (mem_erase.mp hj').1
      simp only [Function.update_of_ne hji]
      exact (ha j hj').congr (fun f hf => (hjs J f (touch_subset_touches _ _ hj' hf)).symm)

theorem base_equivalence_numeric (hn : 1 ≤ n) (hbound : GiantBound n M) (vstar : Vertex n)
    (φ : Counting.Formula AnalysisSymbol (Fin M)) (hφ : φ.free = ∅)
    (a : Fin M → Atom (0 : Vertex n → Scalar))
    (a' : Fin M → Atom (Pi.single vstar 1)) :
    φ.eval (analysisStructure (0 : Vertex n → Scalar)) a ↔
      φ.eval (analysisStructure (Pi.single vstar 1)) a' := by
  have heq : ∀ (names : Finset (Fin M)) (v : Fin M → Atom (0 : Vertex n → Scalar))
      (w : Fin M → Atom (Pi.single vstar 1)), CompatibleAssignment names v w → ∀ i ∈ names, ∀ j ∈ names,
      (v i = v j ↔ w i = w j) := by
    intro names v w ⟨t,x,hg,hb,ha⟩ i hi j hj
    exact (ha i hi).equal_iff (ha j hj)
  have hrel : ∀ (names : Finset (Fin M)) (v : Fin M → Atom (0 : Vertex n → Scalar))
      (w : Fin M → Atom (Pi.single vstar 1)), CompatibleAssignment names v w → ∀ r i, i ∈ names → ∀ j, j ∈ names →
      ((analysisStructure (0 : Vertex n → Scalar)).rel r (v i) (v j) ↔
      (analysisStructure (Pi.single vstar 1)).rel r (w i) (w j)) := by
    intro names v w ⟨t,x,hg,hb,ha⟩ r i hi j hj
    exact (ha i hi).analysisRelation (ha j hj) r
  apply Counting.Formula.eval_of_partialBijectionSystem _ _ CompatibleAssignment heq hrel
    (fun names v w hh i => CompatibleAssignment.extend hn hbound names v w hh i) φ ∅ a a' _ (by simp [hφ])
  refine ⟨0,vstar,?_,by simp,by simp⟩
  simpa [touches] using grid_empty_giant vstar

end CPTSeparation.Grid

end

end OAI
