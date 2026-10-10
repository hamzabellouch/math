import Mathlib
import OAI.Probability.ThorpRouting.Tail.TailShapes

namespace OAI

namespace ThorpNine.Tail

namespace Thorp.StrongTail
open scoped BigOperators Classical
open Specht

noncomputable def tailCellEquiv (μ : YoungDiagram) : Cell (tailDiagram μ) ≃ TailCell μ where
  toFun x := ⟨⟨(x.1.1+1,x.1.2),(mem_tailDiagram μ _ _).mp x.2⟩,by simp [row]⟩
  invFun x := ⟨(row x.1-1,col x.1),(mem_tailDiagram μ _ _).mpr (by
    have he : row x.1-1+1 = row x.1 := by have := x.2; omega
    change (row x.1-1+1,col x.1) ∈ μ
    rw [he]
    exact x.1.2)⟩
  left_inv x := by apply Subtype.ext; simp [row,col]
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · change row x.1-1+1 = row x.1
      have := x.2; omega
    · rfl

noncomputable abbrev upCell (μ : YoungDiagram) (x : Cell (tailDiagram μ)) : Cell μ := (tailCellEquiv μ x).1

@[simp] lemma upCell_row (μ : YoungDiagram) (x : Cell (tailDiagram μ)) : row (upCell μ x) = row x+1 := rfl
@[simp] lemma upCell_col (μ : YoungDiagram) (x : Cell (tailDiagram μ)) : col (upCell μ x) = col x := rfl

lemma tail_card_eq (μ : YoungDiagram) : (tailDiagram μ).card = μ.card-μ.rowLen 0 := by
  rw [←card_cell, Fintype.card_congr (tailCellEquiv μ), tail_card]

noncomputable def extendPerm (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ))) :
    Equiv.Perm (Cell μ) := p.extendDomain (tailCellEquiv μ)

@[simp] lemma extendPerm_up (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ)))
    (x : Cell (tailDiagram μ)) : extendPerm μ p (upCell μ x) = upCell μ (p x) :=
  Equiv.Perm.extendDomain_apply_image p (tailCellEquiv μ) x

lemma extendPerm_top (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ)))
    (x : Cell μ) (hx : row x=0) : extendPerm μ p x = x :=
  Equiv.Perm.extendDomain_apply_not_subtype p (tailCellEquiv μ) (not_not.mpr hx)

@[simp] lemma extendPerm_inv (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ))) :
    (extendPerm μ p)⁻¹ = extendPerm μ p⁻¹ := Equiv.Perm.extendDomain_symm _ _

@[simp] lemma extendPerm_sign (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ))) :
    permSign (extendPerm μ p) = permSign p := by
  simp [extendPerm,permSign,Equiv.Perm.sign_extendDomain]

noncomputable def liftRows (μ : YoungDiagram) (f : Tabloid (tailDiagram μ)) (x : Cell μ) : Fin (μ.colLen 0) :=
  if hx : row x ≠ 0 then
    ⟨(f.1 ((tailCellEquiv μ).symm ⟨x,hx⟩)).val+1,by
      have h := (f.1 ((tailCellEquiv μ).symm ⟨x,hx⟩)).isLt
      have hh := tail_height μ
      omega⟩
  else rowIndex x

@[simp] lemma liftRows_up (μ : YoungDiagram) (f : Tabloid (tailDiagram μ))
    (x : Cell (tailDiagram μ)) : (liftRows μ f (upCell μ x)).val = (f.1 x).val+1 := by
  simp [liftRows,upCell]

lemma liftRows_top (μ : YoungDiagram) (f : Tabloid (tailDiagram μ)) (x : Cell μ) (hx : row x=0) :
    liftRows μ f x = rowIndex x := by simp [liftRows,hx]

lemma liftRows_perm (μ : YoungDiagram) (f : Tabloid (tailDiagram μ))
    (p : Equiv.Perm (Cell (tailDiagram μ))) (hf : f.1 = rowIndex ∘ p) :
    liftRows μ f = rowIndex ∘ extendPerm μ p := by
  funext x
  by_cases hx : row x = 0
  · simp [liftRows_top μ f x hx,extendPerm_top μ p x hx]
  · let y := (tailCellEquiv μ).symm ⟨x,hx⟩
    have he : upCell μ y = x := congrArg Subtype.val ((tailCellEquiv μ).apply_symm_apply ⟨x,hx⟩)
    rw [←he]
    apply Fin.ext
    simp [hf,Function.comp_apply,rowIndex]

noncomputable def liftTabloid (μ : YoungDiagram) (f : Tabloid (tailDiagram μ)) : Tabloid μ :=
  ⟨liftRows μ f, by obtain ⟨p,hp⟩ := f.2; exact ⟨extendPerm μ p,liftRows_perm μ f p hp⟩⟩

@[simp] lemma liftTabloid_base (μ : YoungDiagram) :
    liftTabloid μ (baseTabloid (tailDiagram μ)) = baseTabloid μ := by
  apply Subtype.ext
  funext x
  by_cases hx : row x=0
  · exact liftRows_top μ _ x hx
  · let y := (tailCellEquiv μ).symm ⟨x,hx⟩
    have he : upCell μ y = x := congrArg Subtype.val ((tailCellEquiv μ).apply_symm_apply ⟨x,hx⟩)
    rw [←he]
    apply Fin.ext
    exact liftRows_up μ _ y

lemma liftTabloid_action (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ)))
    (f : Tabloid (tailDiagram μ)) :
    liftTabloid μ (tabloidAct p f) = tabloidAct (extendPerm μ p) (liftTabloid μ f) := by
  apply Subtype.ext
  funext x
  change liftRows μ (tabloidAct p f) x = liftRows μ f ((extendPerm μ p)⁻¹ x)
  rw [extendPerm_inv]
  by_cases hx : row x=0
  · rw [extendPerm_top μ p⁻¹ x hx,liftRows_top μ _ x hx,liftRows_top μ _ x hx]
  · let y := (tailCellEquiv μ).symm ⟨x,hx⟩
    have he : upCell μ y = x := congrArg Subtype.val ((tailCellEquiv μ).apply_symm_apply ⟨x,hx⟩)
    rw [←he,extendPerm_up]
    apply Fin.ext
    simp only [liftRows_up,tabloidAct_apply]

noncomputable def restrictTabloids (μ : YoungDiagram) :
    (Tabloid μ → ℂ) →ₗ[ℂ] (Tabloid (tailDiagram μ) → ℂ) where
  toFun v := fun f => v (liftTabloid μ f)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma restrict_action (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ)))
    (v : Tabloid μ → ℂ) :
    restrictTabloids μ (tabloidRep μ (extendPerm μ p) v) =
      tabloidRep (tailDiagram μ) p (restrictTabloids μ v) := by
  ext f
  change v (tabloidAct (extendPerm μ p)⁻¹ (liftTabloid μ f)) = v (liftTabloid μ (tabloidAct p⁻¹ f))
  rw [extendPerm_inv,liftTabloid_action]

lemma extend_colGroup (μ : YoungDiagram) (c : colGroup (tailDiagram μ)) :
    extendPerm μ c ∈ colGroup μ := by
  intro x
  by_cases hx : row x=0
  · rw [extendPerm_top μ c x hx]
  · let y := (tailCellEquiv μ).symm ⟨x,hx⟩
    have he : upCell μ y = x := congrArg Subtype.val ((tailCellEquiv μ).apply_symm_apply ⟨x,hx⟩)
    rw [←he,extendPerm_up,upCell_col,upCell_col]
    exact c.2 y

lemma restrict_polytabloid (μ : YoungDiagram) :
    restrictTabloids μ (polytabloid μ) = polytabloid (tailDiagram μ) := by
  let v := restrictTabloids μ (polytabloid μ)
  have hv (c : colGroup (tailDiagram μ)) :
      tabloidRep (tailDiagram μ) c v = permSign (c:Equiv.Perm (Cell (tailDiagram μ))) • v := by
    rw [←restrict_action]
    rw [polytabloid_col_action μ ⟨extendPerm μ c,extend_colGroup μ c⟩]
    simp only [map_smul,extendPerm_sign]
    rfl
  have ha : alternator (colGroup (tailDiagram μ)) (tabloidRep (tailDiagram μ)) v =
      (Fintype.card (colGroup (tailDiagram μ)):ℂ) • v := by
    simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply,hv,smul_smul,permSign_sq,one_smul]
    ext f
    simp
  have hb : v (baseTabloid (tailDiagram μ)) = 1 := by
    change polytabloid μ (liftTabloid μ (baseTabloid (tailDiagram μ))) = 1
    rw [liftTabloid_base, polytabloid_base]
  have he := alternator_rank_one_exact (tailDiagram μ) v
  rw [ha] at he
  simp only [Pi.smul_apply,hb,smul_eq_mul,mul_one] at he
  have hc : (Fintype.card (colGroup (tailDiagram μ)):ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (smul_right_injective _ hc) he

lemma tail_space_le_image (μ : YoungDiagram) :
    space (tailDiagram μ) ≤ (space μ).map (restrictTabloids μ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p,rfl⟩
  refine ⟨tabloidRep μ (extendPerm μ p) (polytabloid μ), orbit_mem_space μ _, ?_⟩
  rw [restrict_action,restrict_polytabloid]

theorem tail_dimension_le (μ : YoungDiagram) :
    Module.finrank ℂ (space (tailDiagram μ)) ≤ Module.finrank ℂ (space μ) :=
  (Submodule.finrank_mono (tail_space_le_image μ)).trans (Submodule.finrank_map_le _ _)

end Thorp.StrongTail

namespace Thorp.ButterflyReverse
open scoped BigOperators

abbrev Site (d : ℕ) := {t : Fin d × Card d // t.2 t.1 = false}

def site : (d : ℕ) → SwitchIndex d → Site d
  | 0, t => nomatch t
  | _+1, Sum.inl y => ⟨(0, Fin.cons false y), rfl⟩
  | d+1, Sum.inr (b,t) =>
      ⟨((site d t).1.1.succ, Fin.cons b (site d t).1.2), (site d t).2⟩

lemma site_injective (d : ℕ) : Function.Injective (site d) := by
  induction d with
  | zero => intro t; exact Empty.elim t
  | succ d ih =>
    intro s t h
    cases s with
    | inl y =>
      cases t with
      | inl z =>
        have he := congrArg (fun a : Site (d+1) => Fin.tail a.1.2) h
        exact congrArg Sum.inl he
      | inr t =>
        have he := congrArg (fun a : Site (d+1) => a.1.1.val) h
        simp [site] at he
    | inr s =>
      cases t with
      | inl y =>
        have he := congrArg (fun a : Site (d+1) => a.1.1.val) h
        simp [site] at he
      | inr t =>
        obtain ⟨b,s⟩ := s
        obtain ⟨c,t⟩ := t
        have hbc := congrArg (fun a : Site (d+1) => a.1.2 0) h
        simp only [site, Fin.cons_zero] at hbc
        have hst : site d s = site d t := by
          apply Subtype.ext
          apply Prod.ext
          · exact Fin.succ_inj.mp (congrArg (fun a : Site (d+1) => a.1.1) h)
          · exact congrArg (fun a : Site (d+1) => Fin.tail a.1.2) h
        cases hbc
        cases ih hst
        rfl

lemma site_surjective (d : ℕ) : Function.Surjective (site d) := by
  induction d with
  | zero => intro t; exact Fin.elim0 t.1.1
  | succ d ih =>
    rintro ⟨⟨i,x⟩,hx⟩
    refine Fin.cases ?_ (fun j => ?_) i hx
    · intro hx0
      refine ⟨Sum.inl (Fin.tail x), ?_⟩
      apply Subtype.ext
      simp only [site, Prod.mk.injEq, true_and]
      rw [←hx0,Fin.cons_self_tail]
    · intro hxj
      obtain ⟨t,ht⟩ := ih ⟨(j,Fin.tail x),hxj⟩
      refine ⟨Sum.inr (x 0,t), ?_⟩
      apply Subtype.ext
      simp only [site,ht,Fin.cons_self_tail]

noncomputable def siteEquiv (d : ℕ) : SwitchIndex d ≃ Site d :=
  Equiv.ofBijective (site d) ⟨site_injective d,site_surjective d⟩

def reverseCard (d : ℕ) : Equiv.Perm (Card d) where
  toFun x := fun i => x i.rev
  invFun x := fun i => x i.rev
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

@[simp] lemma reverseCard_apply (d : ℕ) (x : Card d) (i : Fin d) :
    reverseCard d x i = x i.rev := rfl

@[simp] lemma reverseCard_involutive (d : ℕ) (x : Card d) :
    reverseCard d (reverseCard d x) = x := by funext i; simp

def mirrorSite (d : ℕ) : Equiv.Perm (Site d) where
  toFun s := ⟨(s.1.1.rev,reverseCard d s.1.2),by simpa using s.2⟩
  invFun s := ⟨(s.1.1.rev,reverseCard d s.1.2),by simpa using s.2⟩
  left_inv s := by apply Subtype.ext; simp
  right_inv s := by apply Subtype.ext; simp

noncomputable def mirrorSwitch (d : ℕ) : Equiv.Perm (SwitchIndex d) :=
  (siteEquiv d).trans ((mirrorSite d).trans (siteEquiv d).symm)

lemma site_mirrorSwitch (d : ℕ) (t : SwitchIndex d) :
    site d (mirrorSwitch d t) = mirrorSite d (site d t) := by
  exact (siteEquiv d).apply_symm_apply _

lemma routeDomain_site (d : ℕ) (x y : Card d) (t : SwitchIndex d) :
    t ∈ routeDomain d x y ↔
      ∀ j : Fin d, j ≠ (site d t).1.1 →
      (site d t).1.2 j = if j < (site d t).1.1 then x j else y j := by
  classical
  induction d with
  | zero => exact Empty.elim t
  | succ d ih =>
    cases t with
    | inl z =>
      change Sum.inl z ∈ (insert (Sum.inl (Fin.tail y))
        ((routeDomain d (Fin.tail x) (Fin.tail y)).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
        Finset (Sum (Card d) (Bool × SwitchIndex d))) ↔ _
      simp only [Finset.mem_insert, Sum.inl.injEq,Finset.mem_image,
        reduceCtorEq,and_false,exists_false,or_false]
      constructor
      · intro hz j hj
        subst z
        have hj0 : j ≠ 0 := hj
        obtain ⟨i,rfl⟩ := Fin.eq_succ_of_ne_zero hj0
        simp [site,Fin.tail]
      · intro h
        funext j
        have he := h j.succ (by simp [site])
        simpa [site,Fin.tail] using he
    | inr z =>
      obtain ⟨b,t⟩ := z
      change Sum.inr (b,t) ∈ (insert (Sum.inl (Fin.tail y))
        ((routeDomain d (Fin.tail x) (Fin.tail y)).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
        Finset (Sum (Card d) (Bool × SwitchIndex d))) ↔ _
      simp only [Finset.mem_insert,reduceCtorEq,false_or,Finset.mem_image,Sum.inr.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨s,hs,hb,ht⟩
        subst s
        have hst := (ih (Fin.tail x) (Fin.tail y) t).mp hs
        intro j hj
        refine Fin.cases ?_ (fun i => ?_) j hj
        · intro _
          simp [site,hb]
        · intro hi
          have hi' : i ≠ (site d t).1.1 := by simpa [site] using hi
          simpa [site,Fin.tail] using hst i hi'
      · intro h
        have hb := h 0 (by simpa only [site] using (Fin.succ_ne_zero (site d t).1.1).symm)
        have hb' : x 0 = b := by simpa [site] using hb.symm
        refine ⟨t,?_,hb',rfl⟩
        apply (ih (Fin.tail x) (Fin.tail y) t).mpr
        intro j hj
        have he := h j.succ (by simpa [site] using hj)
        simpa [site,Fin.tail] using he

lemma routeValue_site (d : ℕ) (x y : Card d) (t : SwitchIndex d) :
    routeValue d x y t = Bool.xor (x (site d t).1.1) (y (site d t).1.1) := by
  induction d with
  | zero => exact Empty.elim t
  | succ d ih =>
    cases t with
    | inl z => rfl
    | inr z => exact ih (Fin.tail x) (Fin.tail y) z.2

lemma mirrorSwitch_involutive (d : ℕ) (t : SwitchIndex d) :
    mirrorSwitch d (mirrorSwitch d t) = t := by
  apply site_injective d
  rw [site_mirrorSwitch,site_mirrorSwitch]
  apply Subtype.ext
  simp [mirrorSite]

lemma mirror_routeDomain (d : ℕ) (x y : Card d) (t : SwitchIndex d)
    (ht : t ∈ routeDomain d x y) :
    mirrorSwitch d t ∈ routeDomain d (reverseCard d y) (reverseCard d x) := by
  rw [routeDomain_site,site_mirrorSwitch]
  intro j hj
  have hj' : j.rev ≠ (site d t).1.1 := by
    intro h
    apply hj
    change j = (site d t).1.1.rev
    rw [←h,Fin.rev_rev]
  have he := (routeDomain_site d x y t).mp ht j.rev hj'
  change (site d t).1.2 j.rev =
    if j < (site d t).1.1.rev then y j.rev else x j.rev
  rw [he]
  have hord : j < (site d t).1.1.rev ↔ ¬j.rev < (site d t).1.1 := by
    rw [Fin.lt_rev_iff]
    constructor
    · intro h
      exact not_lt_of_ge h.le
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hj')
  by_cases h : j.rev < (site d t).1.1 <;> simp [h,hord]

lemma mirror_routeValue (d : ℕ) (x y : Card d) (t : SwitchIndex d) :
    routeValue d (reverseCard d y) (reverseCard d x) (mirrorSwitch d t) =
      routeValue d x y t := by
  rw [routeValue_site,routeValue_site,site_mirrorSwitch]
  simp only [mirrorSite,Equiv.coe_fn_mk,reverseCard_apply,Fin.rev_rev]
  exact Bool.xor_comm _ _

noncomputable def mirrorCoins (d : ℕ) : Equiv.Perm (SwitchIndex d → Bool) where
  toFun ω := fun t => ω (mirrorSwitch d t)
  invFun ω := fun t => ω (mirrorSwitch d t)
  left_inv ω := by funext t; change ω (mirrorSwitch d (mirrorSwitch d t)) = ω t; rw [mirrorSwitch_involutive]
  right_inv ω := by funext t; change ω (mirrorSwitch d (mirrorSwitch d t)) = ω t; rw [mirrorSwitch_involutive]

lemma mirror_endpoint (d : ℕ) (ω : SwitchIndex d → Bool) (x y : Card d)
    (hxy : butterflyPerm d (decodeButterfly d ω) x = y) :
    butterflyPerm d (decodeButterfly d (mirrorCoins d ω)) (reverseCard d y) =
      reverseCard d x := by
  apply (butterfly_endpoint_iff d _ _ _).mpr
  intro t ht
  have ht' := mirror_routeDomain d (reverseCard d y) (reverseCard d x) t ht
  simp only [reverseCard_involutive] at ht'
  have he := (butterfly_endpoint_iff d ω x y).mp hxy (mirrorSwitch d t) ht'
  change ω (mirrorSwitch d t) = _
  rw [he]
  have hv := mirror_routeValue d x y (mirrorSwitch d t)
  rw [mirrorSwitch_involutive] at hv
  exact hv.symm

lemma butterfly_mirror (d : ℕ) (ω : SwitchIndex d → Bool) :
    butterflyPerm d (decodeButterfly d (mirrorCoins d ω)) =
      reverseCard d * (butterflyPerm d (decodeButterfly d ω))⁻¹ * reverseCard d := by
  apply Equiv.ext
  intro x
  have he := mirror_endpoint d ω
    ((butterflyPerm d (decodeButterfly d ω))⁻¹ (reverseCard d x)) (reverseCard d x)
    (Equiv.apply_symm_apply _ _)
  simpa only [reverseCard_involutive,Equiv.Perm.mul_apply] using he

def reverseOrder (d : ℕ) : Equiv.Perm (Fin d) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

lemma relabel_mul (d : ℕ) (a b : Equiv.Perm (Fin d)) :
    StrongSmoothing.coordinateRelabel d (a*b) =
      StrongSmoothing.coordinateRelabel d a * StrongSmoothing.coordinateRelabel d b := rfl

lemma relabel_reverse (d : ℕ) :
    StrongSmoothing.coordinateRelabel d (reverseOrder d) = reverseCard d := rfl

lemma reverseCard_sq (d : ℕ) : reverseCard d * reverseCard d = 1 := by
  ext x i
  simp

lemma sweep_mirror (d : ℕ) (order : Equiv.Perm (Fin d)) (ω : SwitchIndex d → Bool) :
    StrongSmoothing.sweep d (order*reverseOrder d) (mirrorCoins d ω) =
      (StrongSmoothing.sweep d order ω)⁻¹ := by
  simp only [StrongSmoothing.sweep,relabel_mul,relabel_reverse,butterfly_mirror,mul_inv_rev]
  have hR : (reverseCard d)⁻¹ = reverseCard d := by
    exact inv_eq_of_mul_eq_one_right (reverseCard_sq d)
  rw [hR]
  calc
    _ = StrongSmoothing.coordinateRelabel d order *
        (reverseCard d*reverseCard d) *
        (butterflyPerm d (decodeButterfly d ω))⁻¹ *
        (reverseCard d*reverseCard d) * (StrongSmoothing.coordinateRelabel d order)⁻¹ := by group
    _ = _ := by rw [reverseCard_sq]; group

lemma sweepKernel_reverse (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    StrongSmoothing.sweepKernel d l (order*reverseOrder d) =
      (StrongSmoothing.sweepKernel d l order).transpose := by
  classical
  rw [StrongSmoothing.sweepKernel_law,StrongSmoothing.sweepKernel_law,
    ←StrongSmoothing.PermLaw.inverse]
  ext x y
  unfold StrongSmoothing.PermLaw.kernel
  rw [finiteMean_equiv (mirrorCoins d)]
  apply finiteMean_congr
  intro ω
  change (if StrongSmoothing.tuplePerm
      (StrongSmoothing.sweep d (order*reverseOrder d) (mirrorCoins d ω)) x = y then (1:ℝ) else 0) = _
  rw [sweep_mirror,StrongSmoothing.tuplePerm_inverse]

lemma reflectedKernel_reverse (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    StrongSmoothing.reflectedKernel d l order true =
      StrongSmoothing.reflectedKernel d l (order*reverseOrder d) false := by
  simp only [StrongSmoothing.reflectedKernel,Bool.false_eq_true,
    ↓reduceIte,sweepKernel_reverse,Matrix.transpose_transpose]

end Thorp.ButterflyReverse

namespace Thorp.StrongTail
open scoped BigOperators Classical

section
open StrongSmoothing

lemma reflected_nonneg_both (d l : ℕ) (order : Equiv.Perm (Fin d)) (rev : Bool)
    (x y : Tuples d l) : 0 ≤ reflectedKernel d l order rev x y := by
  cases rev
  · exact reflected_nonneg _ _ _ _ _
  · rw [ButterflyReverse.reflectedKernel_reverse]
    exact reflected_nonneg _ _ _ _ _

lemma reflected_symm_both (d l : ℕ) (order : Equiv.Perm (Fin d)) (rev : Bool) :
    (reflectedKernel d l order rev).IsSymm := by
  cases rev
  · exact reflected_symmetric _ _ _
  · rw [ButterflyReverse.reflectedKernel_reverse]
    exact reflected_symmetric _ _ _

lemma reflected_moment_both (d l : ℕ) (order : Equiv.Perm (Fin d)) (rev : Bool)
    (x : Tuples d l) :
    finiteMean (fun y : Tuples d l =>
      ((Fintype.card (Tuples d l):ℝ)*reflectedKernel d l order rev x y)^(1+(1/1000:ℝ))) ≤
      Real.exp (l*(1+heightDecay 1)) := by
  cases rev
  · exact reflected_moment _ _ _ _
  · rw [ButterflyReverse.reflectedKernel_reverse]
    exact reflected_moment _ _ _ _

lemma reflected_moment_small (d l : ℕ) (order : Equiv.Perm (Fin d)) (rev : Bool)
    (x : Tuples d l) {p : ℝ} (hp : 0 < p) (hpq : p ≤ 1+(1/1000:ℝ)) :
    finiteMean (fun y : Tuples d l =>
      ((Fintype.card (Tuples d l):ℝ)*reflectedKernel d l order rev x y)^p) ≤
      Real.exp (l*(1+heightDecay 1)) := by
  let : Nonempty (Tuples d l) := ⟨x⟩
  let q : ℝ := 1+1/1000
  let f := fun y : Tuples d l => (Fintype.card (Tuples d l):ℝ)*reflectedKernel d l order rev x y
  have hf : ∀ y, 0 ≤ f y := fun y => mul_nonneg (Nat.cast_nonneg _) (reflected_nonneg_both _ _ _ _ _ _)
  have hq : 0 < q := by norm_num [q]
  have hr : 0 ≤ p/q := (div_pos hp hq).le
  have hr1 : p/q ≤ 1 := (div_le_one hq).mpr hpq
  have he (y) : (f y)^p = ((f y)^q)^(p/q) := by
    rw [←Real.rpow_mul (hf y)]
    congr 1
    field_simp
  simp_rw [show (fun y : Tuples d l => ((Fintype.card (Tuples d l):ℝ)*reflectedKernel d l order rev x y)^p)
    = fun y => ((f y)^q)^(p/q) from funext he]
  apply (mean_rpow_concave _ (fun y => Real.rpow_nonneg (hf y) _) hr hr1).trans
  apply (Real.rpow_le_rpow (finiteMean_nonneg (fun y => Real.rpow_nonneg (hf y) _))
    (reflected_moment_both d l order rev x) hr).trans
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  apply Real.exp_le_exp.mpr
  have hA : 0 ≤ (l:ℝ)*(1+heightDecay 1) := by
    have hh := heightDecay_nonneg 1
    positivity
  nlinarith

lemma log_factorial_le_power (n N : ℕ) (hn : n ≤ N) (_hN : 0 < N) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log N := by
  have hb : (n.factorial:ℝ) ≤ (N:ℝ)^n := by
    exact_mod_cast (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left hn n)
  simpa only [Real.log_pow] using Real.log_le_log (by positivity : (0:ℝ)<n.factorial) hb

lemma log_normalization_le (N l : ℕ) (hN : 0 < N) (hl : l ≤ N) :
    Real.log ((N:ℝ)^l/(N.descFactorial l:ℝ)) ≤ 2*l := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hMp : (0:ℝ)<N.descFactorial l := by exact_mod_cast Nat.descFactorial_pos.mpr hl
  rw [Real.log_div (by positivity) hMp.ne',Real.log_pow]
  by_cases hlow : 2*l ≤ N
  · have hhalf : (N:ℝ)/2 ≤ (N+1-l:ℕ) := by
      have hNat : N ≤ 2*(N+1-l) := by omega
      exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by simpa only [mul_comm] using (show (N:ℝ) ≤ 2*(N+1-l:ℕ) by exact_mod_cast hNat))
    have hb : ((N:ℝ)/2)^l ≤ (N.descFactorial l:ℝ) := by
      apply (pow_le_pow_left₀ (by positivity) hhalf l).trans
      exact_mod_cast Nat.pow_sub_le_descFactorial N l
    have hh := Real.log_le_log (pow_pos (by positivity : (0:ℝ)<(N:ℝ)/2) l) hb
    rw [Real.log_pow,Real.log_div hNp.ne' (by norm_num)] at hh
    have ht : Real.log (2:ℝ) ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    nlinarith [(show (0:ℝ) ≤ l by positivity)]
  · have he : (N.descFactorial l:ℝ)*(Nat.factorial (N-l):ℝ) = N.factorial := by
      have he := Nat.factorial_mul_descFactorial hl
      exact_mod_cast (by simpa only [mul_comm] using he : N.descFactorial l * (N-l).factorial = N.factorial)
    have hh := congrArg Real.log he
    rw [Real.log_mul hMp.ne' (by positivity)] at hh
    have hfull := log_factorial_lower (show 1 ≤ N by omega)
    have hrem := log_factorial_le_power (N-l) N (Nat.sub_le _ _) hN
    rw [Nat.cast_sub hl] at hrem
    have hNle : (N:ℝ) ≤ 2*l := by exact_mod_cast (by omega : N ≤ 2*l)
    linarith

lemma normalized_moment_identity {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) {N : ℝ} (hN : 0 < N) (p : ℝ) :
    N⁻¹*(∑ x, (N*f x)^p) =
     (N/(Fintype.card X:ℝ))^(p-1) * finiteMean (fun x => ((Fintype.card X:ℝ)*f x)^p) := by
  let M : ℝ := Fintype.card X
  have hM : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
  have he (x) : (N*f x)^p = (N/M)^p*(M*f x)^p := by
    rw [←Real.mul_rpow (div_nonneg hN.le hM.le) (mul_nonneg hM.le (hf x))]
    congr 1
    field_simp
  simp_rw [he]
  rw [←Finset.mul_sum,Real.rpow_sub (div_pos hN hM),Real.rpow_one]
  unfold finiteMean
  dsimp [M] at hM ⊢
  field_simp

lemma density_at_small_exponent {p : ℝ} (hp : 1 < p) (hpq : p ≤ 1+(1/1000:ℝ)) :
    DensityAt p (3+heightDecay 1) := by
  intro d l hl order rev x
  dsimp only
  let : Nonempty (Tuples d l) := ⟨x⟩
  let H := reflectedKernel d l order rev
  have hm := reflected_moment_small d l order rev x (by linarith : 0<p) hpq
  have hb : Real.exp ((l:ℝ)*(1+heightDecay 1)) ≤ Real.exp ((3+heightDecay 1)*l) := by
    apply Real.exp_le_exp.mpr
    nlinarith [(show (0:ℝ) ≤ l by positivity)]
  have hs (y) : reflectedKernel d l order rev y x = reflectedKernel d l order rev x y := (reflected_symm_both d l order rev).apply _ _
  have hpow : (((2:ℝ)^d)^l)⁻¹ * (∑ y, ((((2:ℝ)^d)^l)*H x y)^p) ≤
      Real.exp ((3+heightDecay 1)*l) := by
    rw [normalized_moment_identity (fun y => H x y) (reflected_nonneg_both d l order rev x)
      (by positivity) p]
    have hrat : ((2:ℝ)^d)^l/(Fintype.card (Tuples d l):ℝ) ≤ Real.exp (2*l) := by
      apply (Real.log_le_iff_le_exp (by positivity)).mp
      rw [tuples_card]
      exact_mod_cast log_normalization_le (2^d) l (by positivity) hl
    have hr : 0 ≤ ((2:ℝ)^d)^l/(Fintype.card (Tuples d l):ℝ) := by positivity
    have hrp : (((2:ℝ)^d)^l/(Fintype.card (Tuples d l):ℝ))^(p-1) ≤ Real.exp (2*l) := by
      apply (Real.rpow_le_rpow hr hrat (by linarith)).trans
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      apply Real.exp_le_exp.mpr
      have hpl : p-1 ≤ 1 := by linarith
      nlinarith [(show (0:ℝ) ≤ l by positivity)]
    apply (mul_le_mul hrp hm (finiteMean_nonneg (fun y => Real.rpow_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (reflected_nonneg_both d l order rev x y)) _)) (Real.exp_pos _).le).trans
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf
    rfl
  dsimp [H] at hpow
  refine ⟨hm.trans hb,?_,hpow,?_⟩
  · simpa only [hs] using hm.trans hb
  · simpa only [hs] using hpow

end
open Specht UnitaryFinite

lemma dimension_le_factorial (μ : YoungDiagram) :
    Module.finrank ℂ (space μ) ≤ μ.card.factorial := by
  have hdim : Module.finrank ℂ (space μ) ≤ Fintype.card (Tabloid μ) := by
    simpa using Submodule.finrank_le (space μ)
  have hrow : 1 ≤ Fintype.card (rowGroup μ) := Fintype.card_pos
  have hc := card_tabloid_mul_row μ
  nlinarith

lemma tail_card_exact (μ : YoungDiagram) :
    (tailDiagram μ).card = μ.card - μ.rowLen 0 := by
  rw [←card_cell,Fintype.card_congr (tailCellEquiv μ),tail_card]

lemma tail_dimension_le_factorial (μ : YoungDiagram) :
    Module.finrank ℂ (space (tailDiagram μ)) ≤ (μ.card - μ.rowLen 0).factorial := by
  simpa only [tail_card_exact] using dimension_le_factorial (tailDiagram μ)

lemma sweep_sq_palindrome (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ) (rev : Bool) :
    ‖SparseContact.sweepOperator d μ e rev‖^2 =
      ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ := by
  rw [SparseContact.sweep_forward_norm, sampleOperator_palindrome _ _ (relabelledUnitary_unitary μ e)]
  change ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))‖^2 = _
  rw [show (sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint =
    star (sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))) from rfl]
  simpa only [pow_two] using (CStarRing.norm_self_mul_star (x := sampleOperator (V := hilbertSpace μ)
    (relabelledUnitary μ e) (fun ω => butterflyPerm d (decodeButterfly d ω)))).symm

lemma sweep_sq_le_one (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ) (rev : Bool) :
    ‖SparseContact.sweepOperator d μ e rev‖^2 ≤ 1 := by
  have h := SparseContact.sweep_norm_le_one d μ e rev
  nlinarith [norm_nonneg (SparseContact.sweepOperator d μ e rev)]

theorem strong_tail : MainStatement := by
  obtain ⟨a,h,ha,hh,dE⟩ := Specht.spectral_regimes
  obtain ⟨D0,hD0⟩ := Filter.eventually_atTop.mp dE
  let d0 := max D0 1
  let t : ℝ := min a (1/1000)
  have ht : 0 < t := lt_min ha (by norm_num)
  have hta : t ≤ a := min_le_left _ _
  have htq : t ≤ 1/1000 := min_le_right _ _
  let b := t/(1+t)
  have hden : 0 < 1+t := by linarith
  have hb : 0 < b := div_pos ht hden
  have hbt : b ≤ t := (div_le_iff₀ hden).mpr (by nlinarith [sq_nonneg t])
  have hba : b ≤ a := hbt.trans hta
  have hb1 : b ≤ 1 := (div_le_one hden).mpr (by linarith)
  let C := Real.log (((2^d0).factorial:ℕ):ℝ)
  have hC : 0 ≤ C := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos (2^d0))
  refine ⟨1+t,3+heightDecay 1,C,by linarith,by linarith,
    density_at_small_exponent (by linarith) (by linarith),?_⟩
  intro d μ e rev
  let k := μ.card - μ.rowLen 0
  let D : ℝ := Module.finrank ℂ (space (tailDiagram μ))
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast dimension_pos (tailDiagram μ)
  have hDp : 0 < D := by linarith
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  have hμ : μ.card=2^d := by rw [←card_cell,←Fintype.card_congr e,card_positions]
  have hform : -(((1+t)-1)/(1+t)) = -b := by dsimp [b]; congr 1; ring
  rw [hform]
  change ‖SparseContact.sweepOperator d μ e rev‖^2 ≤ Real.exp (C*k)*D^(-b)
  rw [Real.rpow_def_of_pos hDp,←Real.exp_add]
  by_cases hk : k=0
  · have hDone : D=1 := by
      have hn := tail_dimension_le_factorial μ
      change Module.finrank ℂ (space (tailDiagram μ)) ≤ k.factorial at hn
      rw [hk,Nat.factorial_zero] at hn
      have hu : D ≤ 1 := by dsimp [D]; exact_mod_cast hn
      linarith
    rw [hk,Nat.cast_zero,mul_zero,hDone,Real.log_one,zero_mul,add_zero,Real.exp_zero]
    exact sweep_sq_le_one d μ e rev
  · have hkpos : 0<k := by omega
    by_cases hd : d0 ≤ d
    · have hdpos : 0<d := by have := le_max_right D0 1; omega
      by_cases htall : (μ.card:ℝ)/2 < μ.colLen 0
      · rw [sweep_sq_palindrome,Specht.palindrome_tall_zero_general d hdpos μ e htall,
          @norm_zero (hilbertSpace μ →L[ℂ] hilbertSpace μ) _]
        exact (Real.exp_pos _).le
      · have hg := (hD0 d ((le_max_left _ _).trans hd) μ e hkpos (le_of_not_gt htall)).1
        have hrootpos : (0:ℝ)<Module.finrank ℂ (space μ) := by exact_mod_cast dimension_pos μ
        have hlogle : Real.log D ≤ Real.log (Module.finrank ℂ (space μ):ℝ) :=
          Real.log_le_log hDp (by dsimp [D]; exact_mod_cast tail_dimension_le μ)
        rw [sweep_sq_palindrome]
        apply hg.trans
        apply Real.exp_le_exp.mpr
        have hbound := mul_le_mul hba hlogle hlog ha.le
        have hck : 0 ≤ C*(k:ℝ) := mul_nonneg hC (Nat.cast_nonneg _)
        nlinarith
    · have hpow : 2^d ≤ 2^d0 := Nat.pow_le_pow_right (by decide) (by omega)
      have hklarge : k ≤ 2^d0 := (by simp [k,hμ] : k ≤ 2^d).trans hpow
      have hdim : D ≤ ((2^d0).factorial:ℝ) := by
        dsimp [D]
        exact_mod_cast (tail_dimension_le_factorial μ).trans (Nat.factorial_le hklarge)
      have hlC : Real.log D ≤ C := Real.log_le_log hDp hdim
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hkpos
      have hprod : b*Real.log D ≤ C*(k:ℝ) := by nlinarith
      apply (sweep_sq_le_one d μ e rev).trans
      exact Real.one_le_exp_iff.mpr (by nlinarith)

end Thorp.StrongTail

end ThorpNine.Tail

end OAI
